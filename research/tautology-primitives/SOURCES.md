# Sources and research resources

## Primary / foundational

1. Stephen A. Cook, **The Complexity of Theorem-Proving Procedures** (1971):  
   https://www.cs.umd.edu/~gasarch/COURSES/452/F14/cookpaper.pdf

2. Francis Jeffry Pelletier and Norman M. Martin, **Post's Functional Completeness Theorem**, *Notre Dame Journal of Formal Logic* 31(2), 1990:  
   https://www.sfu.ca/~jeffpell/papers/PostPellMartin.pdf

## Logic / Boolean semantics

3. Open Logic Project, **Propositional Logic**:  
   https://builds.openlogicproject.org/content/propositional-logic/propositional-logic.pdf

4. Robert Rynasiewicz, **Boolean Functions and Truth-Functional Completeness**:  
   https://pages.jh.edu/rrynasi1/mathlog1/slides/04_BooleanCompleteness.pdf

5. Max Planck Institute for Informatics automated-reasoning notes:  
   https://www.mpi-inf.mpg.de/fileadmin/inf/rg1/Documents/script-4.pdf

## Boolean clone / composition context

6. Reinhard Pöschel and Ivo Rosenberg, **Compositions and Clones of Boolean Functions**, in *Boolean Models and Methods in Mathematics, Computer Science, and Engineering*.

7. Implication-only Boolean-tree research treating tautologies as formulas computing constant TRUE:  
   https://dmg.tuwien.ac.at/bgitten/preprints/implication.pdf

## Computational cross-check

Wolfram Language documentation:
- `TautologyQ` — https://reference.wolfram.com/language/ref/TautologyQ
- `BooleanFunction` — https://reference.wolfram.com/language/ref/BooleanFunction
- `BooleanMinterms` — https://reference.wolfram.com/language/ref/BooleanMinterms
- `Groupings` — https://reference.wolfram.com/language/ref/Groupings

## Episteme evidence used for architecture transfer

Preserved Episteme factory reports and verification records identify:
- `src/core/81-factory-kernel.js`
- `src/core/82-numeric-factory.js`
- `src/core/83-text-factory.js`
- `src/core/84-bindings-factory.js`
- `src/core/90-builders.js`
- `src/core/95-assembly.js`

These records support architecture transfer only; they are not a substitute for the complete Episteme runtime source package.
