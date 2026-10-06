# Publication and recovery boundary

The public repository contains six original research documents byte-for-byte, plus newly generated navigation, indexes, scope and initialization records. **It does not contain the full original archive or full proof corpus.**

## Original packet

Name: `Knowledge_Decay_Parts_Whole_2026-10-05.zip`  
SHA-256: `60c816fd5be224ff3b13470b71a2c5f846f6db2038c651f7772cf4a696bdc532`  
Availability: attachment in the originating ChatGPT conversation; no public download URL asserted.

## Selected research companion

Name: `Knowledge_Decay_Research_Sources_2026-10-05.tar.xz`  
SHA-256: `2825085a0905112e039ece65c4163e2db3825c7a5dc12919bef32c17b4b56000`  
Size: 72532 bytes.  
Availability: separately delivered in the originating conversation, **not uploaded to this repository**.

It preserves 19 selected original files plus a new manifest: all 64 full claim sections, all 14 selected structured older records, qualifications, the requirement map, and selected source texts. The broad invariant atlas, raw retrieval-response dump and session-specific assembly machinery remain outside the public export.

Every original packet member and its disposition appears in SOURCE_IMPORT.json. A file hash identifies the expected bytes; it does not make an absent file accessible. The source indexes therefore do not claim to be complete proof transcripts.

## Verification

After obtaining the companion from the originating conversation:

```sh
sha256sum Knowledge_Decay_Research_Sources_2026-10-05.tar.xz
mkdir -p .local/source-snapshot
tar -xJf Knowledge_Decay_Research_Sources_2026-10-05.tar.xz -C .local/source-snapshot
```

Read `CLAIM_REGISTER.json` alongside `PROOF_QUALIFICATIONS.txt`. Exact claim source spans resolve to the selected extracted texts. S1's raw-response parent and S2's full atlas remain original-archive-only; do not pretend those parent files are included in the selected companion.

The proof-ledger tail and standalone Stairs of State specification remain unresolved. Repository publication does not close those gaps, confer sole authorship, grant new licensing rights, or verify mathematical or human-benefit claims.
