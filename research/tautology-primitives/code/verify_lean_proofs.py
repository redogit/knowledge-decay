"""Compile FIG-22 proofs with pinned Lean, and reject extra theorem axioms.

Usage: python code/verify_lean_proofs.py --lean /path/to/lean
No packages are downloaded by this command. The ordinary compiler suffices on
normal Linux/macOS hosts. For the observed PID-virtualized host only, a bundled
readlink adapter repairs Lean's self-executable lookup; it does not change proof
elaboration, the kernel, or primitive axioms. The adapter is recorded explicitly.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / 'formal'
MODULES = ('TreeProofs', 'DagProofs', 'BasisCertificates', 'BasisDag', 'Interface',
           'BooleanSupport', 'BooleanDagSupport', 'TheoremTwoUpper',
           'TheoremTwoLower', 'TheoremTwo', 'TheoremTwoConsequences', 'TheoremTwoRaw')
STANDARD_AXIOMS = {'propext', 'Quot.sound', 'Classical.choice'}
VERSION = '4.35.0'
RELEASE_COMMIT = 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc'
ARCHIVE_SHA256 = '7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d'


def strip_comments(source: str) -> str:
    """Remove nested Lean block/line comments and string contents for policy scan."""
    result = []
    i = nesting = 0
    while i < len(source):
        if source.startswith('/-', i):
            nesting += 1
            i += 2
        elif nesting and source.startswith('-/', i):
            nesting -= 1
            i += 2
        elif nesting:
            if source[i] == '\n':
                result.append('\n')
            i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        elif source[i] == '"':
            result.append('""')
            i += 1
            while i < len(source):
                if source[i] == '\\':
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            result.append(source[i])
            i += 1
    if nesting:
        raise RuntimeError('Unterminated Lean block comment')
    return ''.join(result)


def check_source(source: str) -> None:
    forbidden = re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b', strip_comments(source))
    if forbidden:
        raise RuntimeError(f'Forbidden proof source token: {forbidden.group(0)}')


def axioms_from_output(output: str) -> set[str]:
    if 'sorryAx' in output or "declaration uses 'sorry'" in output:
        raise RuntimeError('Lean reported an admitted placeholder')
    found = set()
    for group in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', output):
        found.update(x.strip() for x in group.split(',') if x.strip())
    unexpected = found - STANDARD_AXIOMS
    if unexpected:
        raise RuntimeError(f'Extra theorem axioms: {sorted(unexpected)}')
    return found


def theorem_names(source: str) -> list[str]:
    """Discover public theorem declarations in these deliberately simple modules."""
    names, namespaces = [], []
    for line in strip_comments(source).splitlines():
        line = line.strip()
        namespace = re.match(r'namespace\s+([\w.]+)', line)
        if namespace:
            namespaces.append(namespace.group(1))
            continue
        if re.match(r'end(?:\s+[\w.]+)?\s*$', line):
            if namespaces:
                namespaces.pop()
            continue
        declaration = re.match(r'(?:@\[[^]]+\]\s*)*(?:theorem|lemma)\s+([\w.]+)', line)
        if declaration:
            name = '.'.join([*namespaces, declaration.group(1)])
            if name.startswith('FIG22.'):
                names.append(name)
    return names


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(argv: list[str], *, env: dict, cwd: Path, timeout: int = 300) -> subprocess.CompletedProcess:
    return subprocess.run(argv, cwd=cwd, env=env, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, timeout=timeout, check=False)


def require_false_rejection(result: subprocess.CompletedProcess, name: str) -> None:
    if result.returncode == 0:
        raise RuntimeError(f'Lean unexpectedly accepted false control: {name}')
    if 'Tactic `decide` proved that the proposition' not in result.stdout or 'is false' not in result.stdout:
        raise RuntimeError(f'Control {name} failed for an unexpected reason: {result.stdout}')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', default=shutil.which('lean'))
    args = parser.parse_args()
    if not args.lean:
        raise SystemExit('Lean is not installed/on PATH; install leanprover/lean4:v4.35.0 or pass --lean.')
    lean = str(Path(args.lean).resolve())
    started = datetime.now(timezone.utc).isoformat()
    clock = time.perf_counter()
    sources = [FORMAL / f'{name}.lean' for name in MODULES]
    sources += [FORMAL/'lean-toolchain', FORMAL/'lakefile.lean',
                FORMAL/'runtime/proc_self_path.c', Path(__file__).resolve()]
    for source in sources:
        if not source.is_file():
            raise SystemExit(f'Missing proof input: {source.relative_to(ROOT)}')
    names = []
    for source in sources:
        if source.suffix == '.lean':
            text = source.read_text()
            check_source(text)
            if source.stem in MODULES:
                names += theorem_names(text)
    if not names:
        raise SystemExit('No public FIG22 theorem declarations discovered')
    before = {p: digest(p) for p in sources}
    env = dict(os.environ)
    # Do not accidentally import a stale or unrelated project proof artifact.
    env.pop('LEAN_PATH', None)
    records, combined = [], []
    with tempfile.TemporaryDirectory(prefix='fig22-lean-') as temporary:
        build = Path(temporary)
        version = run([lean, '--version'], env=env, cwd=FORMAL)
        adapter = None
        if version.returncode != 0 and 'failed to locate application' in version.stdout:
            # This checks the observed discrepancy rather than assuming every host
            # needs a compatibility shim. /proc/self/exe is an allowed own-process
            # path; /proc/<getpid>/exe points elsewhere on this particular host.
            try:
                own = os.readlink('/proc/self')
            except OSError:
                own = str(os.getpid())
            if own == str(os.getpid()):
                raise RuntimeError(version.stdout)
            adapter_path = build / 'proc_self_path.so'
            command = ['cc', '-shared', '-fPIC', '-O2', '-Wall', '-Wextra', '-Werror',
                       '-o', str(adapter_path), str(FORMAL/'runtime/proc_self_path.c'), '-ldl']
            compile_adapter = run(command, env=env, cwd=FORMAL)
            if compile_adapter.returncode:
                raise RuntimeError(compile_adapter.stdout)
            adapter = {'reason': 'PID virtualization: getpid and /proc/self disagree',
                       'source': 'formal/runtime/proc_self_path.c',
                       'source_sha256': digest(FORMAL/'runtime/proc_self_path.c'),
                       'shared_library_sha256': digest(adapter_path),
                       'build_command': command, 'compiler': run(['cc','--version'],env=env,cwd=FORMAL).stdout.splitlines()[0],
                       'scope': 'Only own executable-path readlink; official Lean compiler/kernel unmodified'}
            env['LD_PRELOAD'] = str(adapter_path)
            version = run([lean, '--version'], env=env, cwd=FORMAL)
        if version.returncode or f'version {VERSION},' not in version.stdout or RELEASE_COMMIT not in version.stdout:
            raise RuntimeError(f'Unexpected/failing Lean release: {version.stdout}')
        env['LEAN_PATH'] = str(build)
        combined.append('$ lean --version\n' + version.stdout)
        for module in MODULES:
            command = [lean, '-o', str(build/f'{module}.olean'), f'{module}.lean']
            result = run(command, env=env, cwd=FORMAL)
            records.append({'module': module, 'command': command, 'exit_status': result.returncode})
            combined.append('$ ' + ' '.join(command) + '\n' + result.stdout)
            if result.returncode:
                print(result.stdout, end='')
                raise RuntimeError(f'Lean rejected {module}')
        audit = build / 'AxiomAudit.lean'
        audit.write_text(''.join(f'import {m}\n' for m in MODULES) + '\n' +
                         ''.join(f'#print axioms {name}\n' for name in names))
        command = [lean, str(audit)]
        result = run(command, env=env, cwd=build)
        combined.append('$ lean AxiomAudit.lean\n' + result.stdout)
        if result.returncode:
            print(result.stdout, end='')
            raise RuntimeError('Lean axiom audit failed')
        axiom_dependencies = axioms_from_output(result.stdout)
        audited = len(re.findall(r'(?:depends on axioms:|does not depend on any axioms)', result.stdout))
        if audited != len(names):
            raise RuntimeError(f'Incomplete axiom audit: {audited}/{len(names)}')
        negative_controls = []
        controls = {
            'incorrect_nor_formula_cost':
                'example : FIG22.Tree.formulaCost .nor = 4 := by decide\n',
            'incorrect_nor_tautology':
                'example : (∀ b : Bool, FIG22.Tree.apply .nor b b = true) := by decide\n',
            'incorrect_theorem_two_empty_branch':
                'example : FIG22.Basis.TheoremTwo.classify ([] : List FIG22.Basis.Op) = .one := by decide\n',
            'incorrect_theorem_two_shared_branch':
                'example : FIG22.Basis.TheoremTwo.classify ([8, 0] : List FIG22.Basis.Op) = .two := by decide\n',
        }
        for name, claim in controls.items():
            path = build / f'{name}.lean'
            path.write_text('import TheoremTwoRaw\n' + claim)
            rejected = run([lean, str(path)], env=env, cwd=build)
            require_false_rejection(rejected, name)
            combined.append(f'$ lean {name}.lean # EXPECTED REJECTION\n' + rejected.stdout)
            negative_controls.append({'name': name, 'exit_status': rejected.returncode,
                                      'expected_result': 'rejected', 'result': 'rejected'})
        # Preserve the actual generated audit source as a reproducible output.
        (ROOT/'evidence/lean_axiom_audit.lean').write_text(audit.read_text())
    after = {p: digest(p) for p in sources}
    if before != after:
        raise RuntimeError('Proof inputs changed during verification')
    log_path = ROOT/'evidence/lean_proofs.log'
    log_path.write_text('\n'.join(combined), encoding='utf-8')
    outputs = [log_path, ROOT/'evidence/lean_axiom_audit.lean']
    kernel_library = Path(lean).parent.parent/'lib/lean/libleanshared.so'
    manifest = {
        'schema': 'fig22-lean-verification-v1',
        'source_checkpoint': '154d5cb53ad36d8598f6d8239356d2e9d6356a94',
        'started_at': started, 'runtime_seconds': time.perf_counter()-clock,
        'status': 'kernel-checked', 'exit_status': 0,
        'toolchain': {'release': VERSION, 'release_commit': RELEASE_COMMIT,
                      'version_output': version.stdout.strip(), 'executable_sha256': digest(Path(lean)),
                      'kernel_shared_library_sha256': digest(kernel_library) if kernel_library.is_file() else None,
                      'reference_linux_release_archive_sha256': ARCHIVE_SHA256,
                      'release_url': f'https://github.com/leanprover/lean4/releases/tag/v{VERSION}'},
        'runtime_adapter': adapter,
        'environment': {'system': platform.system(), 'machine': platform.machine(),
                        'python': platform.python_version()},
        'commands': records,
        'negative_controls': negative_controls,
        'proof_policy': {'admitted_placeholders': False, 'added_axioms': False,
                         'native_decide': False, 'axiom_dependencies': sorted(axiom_dependencies),
                         'standard_axioms_allowed': sorted(STANDARD_AXIOMS)},
        'public_theorems_audited': names,
        'theorem_count': len(names),
        'scope': ['Full Theorem2 for every subset/list/predicate basis of all binary Boolean functions',
                  'All seven ordered branches, exact costs or unbounded non-generation, and their supporting factors',
                  'Raw-function truth-table bijection, formula/DAG adapters and direct raw-predicate theorem',
                  'No formula optimum four, shared-size equals both depth optima, and sharp finite upper bounds',
                  'Six singleton formula/depth minima over arbitrary finite input dimensions',
                  'Six singleton reachable-DAG minima, including dead allocated gates',
                  'All 136 singleton/pair formula/depth and reachable-DAG minima with kernel certificates',
                  'Unary/source renaming preservation and all43 non-generating basis exclusions'],
        'not_claimed': ['No P-versus-NP result or external runtime admission',
                        'No weighted hardware, higher-arity, or multi-output theorem',
                        'Lean model correctness still requires statement/model review'],
        'inputs': [{'path': str(p.relative_to(ROOT)), 'sha256_before': before[p],
                    'sha256_after': after[p]} for p in sources],
        'outputs': [{'path': str(p.relative_to(ROOT)), 'sha256': digest(p)} for p in outputs],
    }
    (ROOT/'evidence/lean_verification.json').write_text(json.dumps(manifest, indent=2, sort_keys=True)+'\n')
    print(f'Lean {VERSION}: {len(MODULES)} modules compiled; {len(names)} theorem axiom audits passed.')
    print('Axiom dependencies: ' + ', '.join(sorted(axiom_dependencies)))
    print('Theorem2, all supporting Boolean representation factors and arbitrary-basis corollaries: kernel checked.')


if __name__ == '__main__':
    main()
