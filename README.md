# Minimal idempotent subspaces in evolution algebras

**Short note:** [note/note.pdf](note/note.pdf) (3 pages) · Wenlin Zhang and Haobo Ma, The Omega Institute / National University of Singapore

## The question

In *On solvable evolution algebras and a conjecture by García-Martínez and Pérez-Rodríguez* (Meta AI, 2026-10-02), Andres Barei, working with Muse Spark, refutes Conjecture 1.1 of García-Martínez and Pérez-Rodríguez and ends Section 3 with Remark 3.5:

> Given a finite-dimensional evolution algebra E, we are yet to find idempotent subspaces of dimension greater than two which do not properly contain a nontrivial idempotent subspace.

## The answer

Such subspaces exist in every dimension.

- **Dimension 3.** In the five-dimensional complex evolution algebra with natural basis e1,…,e5 and squares e1² = 4u + 2w, e2² = v, e3² = −v, e4² = v + w, e5² = −v − w, where u = e1+…+e5, v = e2 − e3, w = e4 − e5, the subspace V = Span{u, v, w} satisfies V² = V and contains no nonzero proper idempotent subspace. Inside V: u² = 4u + 2w, uv = 2v, uw = 2v + 2w, and Span{v, w} squares to zero.
- **Every dimension d ≥ 2.** The same Jordan-block construction gives a minimal idempotent subspace of dimension d inside an evolution algebra of dimension 2d − 1, and 2d − 1 is the least ambient dimension for this family.
- The note also gives a criterion in complex dimension three for non-solvable, idempotent-free evolution algebras, the minimal dimensions of counterexamples to Conjecture 1.1 over ℚ (two) and ℝ (three), and a counterexample over every field of characteristic two.

## Machine-checked

| File | Statement | Status |
| --- | --- | --- |
| [trureturing `BareiRemarkThreeFive.lean`](https://github.com/the-omega-institute/trureturing/blob/17c79c2f2872ef9c1880cfd7718e4c579279d3a2/D5/S3/QuadraticForms/EvolutionAlgebras/BareiRemarkThreeFive.lean) | Remark 3.5, dimension 3 | frozen in trureturing ([PR #12924](https://github.com/the-omega-institute/trureturing/pull/12924), preregistration [#12879](https://github.com/the-omega-institute/trureturing/issues/12879)) |
| [lean/Extension.lean](lean/Extension.lean) | the same construction, with the intrinsic 3-dimensional algebra | Lean 4 |
| [lean/CharacteristicTwo.lean](lean/CharacteristicTwo.lean) | a non-solvable, idempotent-free evolution algebra over every field of characteristic two | Lean 4 |
| [lean/Certificate.lean](lean/Certificate.lean) | Barei's Example 2.1 (his result): non-solvable with only the zero idempotent, over every field of characteristic ≠ 2 | Lean 4 |

All theorems depend only on `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no `native_decide`. Toolchain `leanprover/lean4:v4.33.0`, Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. Check a file with `lake env lean lean/<file>.lean` inside any Lake project pinned to that Mathlib.

The general-dimension family, its optimality and the dimension-three criterion are written proofs in the note, supported by the exact computations in [scripts/exact_search.py](scripts/exact_search.py) (output: [scripts/exact_results.json](scripts/exact_results.json); requires SymPy).

## Credit

The question is Barei's (with Muse Spark). Concurrent counterexamples to Conjecture 1.1: Xing-Yu Hu and Ran Wen, arXiv:2609.25023. The embedding of commutative algebras into evolution algebras follows the framework of Costoya, Fernández Ouaridi and Viruel, arXiv:2609.32784. The three-dimensional classification is Cabrera Casado, Siles Molina and Velasco, Linear Algebra Appl. 524 (2017). Our literature check is bounded; we make no priority claim.

The results were obtained with AI assistance (Codex) and checked by the Lean kernel and by exact computation; the authors take responsibility for the note.
