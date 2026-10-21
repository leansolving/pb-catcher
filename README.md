# PBLean: VeriPB Proof Certificates for Lean 4

[![CI](https://github.com/leansolving/pblean/actions/workflows/ci.yml/badge.svg)](https://github.com/leansolving/pblean/actions/workflows/ci.yml)
[![Lean](https://img.shields.io/badge/Lean-v4.30.0-blue)](https://github.com/leanprover/lean4/releases/tag/v4.30.0)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-blue.svg)](LICENSE)

**PBLean** provides verified pseudo-Boolean proof checking in Lean 4. Reads [VeriPB](https://gitlab.com/MIAOresearch/software/VeriPB) kernel-format proofs and produces Lean theorems, analogous to `Std.Tactic.BVDecide` (LRAT) but for pseudo-Boolean reasoning. VeriPB's kernel format is the fully-elaborated proof format produced by `veripb --elaborate`, in which every inference step is made explicit. Standalone Lean 4 project with no Mathlib dependency.

**Paper:** S. Szeider. *PBLean: Pseudo-Boolean Proof Certificates for Lean 4.* [arXiv:2602.08692](https://arxiv.org/abs/2602.08692), 2026.

## Architecture

Three-layer design mirroring LRAT:

| Layer | File | Description |
|-------|------|-------------|
| Kernel | `VeriPB/Tactic/Sat/PseudoBoolean.lean` | PB constraint types, evaluation, soundness lemmas |
| Metaprogram | `VeriPB/Tactic/Sat/FromVeriPB.lean` | Parser, normalization, `Expr`-level proof construction |
| Reflection | `VeriPB/Tactic/Sat/ReflectCheck.lean` | Verified checker definitions (pol, RUP, redundance goals) |
| Reflection | `VeriPB/Tactic/Sat/ReflectFast.lean` | Runtime implementation of the checker (`@[implemented_by]`) |
| Reflection | `VeriPB/Tactic/Sat/Reflect.lean` | `checkProofBool`, `proofClaim?`, soundness proofs, `veripb_reflect`, `mkFormulaUnsatProof` |

Verification uses reflection: a Boolean checker with a proved soundness theorem, executed as compiled native code via `native_decide` (same trade-off as `bv_decide`). The verified checker is written over lists for provability; at runtime `@[implemented_by]` swaps in an array-based implementation that must be extensionally equal to it. That equality is tested, not proved: `Tests/Normalize.lean` and `Tests/FastConstr.lean` compare the runtime operations against verbatim copies of the verified definitions on random inputs, and `Tests/Differential.lean` (and `applications/difftest.lean` for the large proofs) runs both checkers side by side and requires identical constraint databases after every proof step.

Downstream projects that produce `formulaUnsat` theorems from their own encodings can call `VeriPB.Reflect.mkFormulaUnsatProof` to build the reflection bridge term instead of assembling it by hand.

`veripb_reflect name "f.opb" "p.pbp"` registers a theorem that matches the proof's conclusion: `formulaUnsat F` for `conclusion UNSAT`, `formulaSatisfiable F` for `conclusion SAT`, and `formulaBounds F obj offset lb ub` for `conclusion BOUNDS lb : id ub` (every solution has objective value at least `lb`, some solution has value at most `ub`; `none` stands for `INF`). The objective in the statement is the normalized min-form objective `objVal obj v + offset` (normalized nonnegative terms `obj`, constant `offset`). For `max: f` the parser negates the objective, as VeriPB does, so the statement is about `−f`: `lb` gives `f ≤ −lb` for every solution and `ub` gives a solution with `f ≥ −ub`. `formulaBounds_optimum` turns equal bounds into the optimum. The conclusion must close the proof as in VeriPB and CakePB: the only `output` line (`output NONE ;`, or an output claim `output DERIVABLE|EQUISATISFIABLE|EQUIOPTIMAL FILE ;` accepted under CakePB's bound-side conditions; the claim about the output formula is not certified, and the message says so), then the only `conclusion` line, then the end line.

## Supported VeriPB rules

`pol` (polynomial arithmetic: `+`, `*`, `d`, `s`, `w` weakening, `-`, `c` division in variable form, `n`/`m` mixed-integer rounding), `rup` (reverse unit propagation), `ia` (implication), `pbc`/`subproof`/`qed` (proof by contradiction), `red` (redundance-based strengthening with explicit subproofs and proof goals), `deld`/`delc` (deletion, including checked core deletion `delc id : witness : subproof`), `core`, `strengthening_to_core`, `sol`/`soli`/`obji` (solution logging and objective-improvement assertions), `eobj`/`obju new|diff` (objective equality and objective updates with core-only subproofs), `f` (formula size), `output NONE` and `output DERIVABLE/EQUISATISFIABLE/EQUIOPTIMAL FILE` (accepted as footers under CakePB's bound-side preconditions; the claim about the output formula itself is not certified, the registered theorem is the conclusion's), `conclusion UNSAT/SAT/BOUNDS/NONE`. Parsed but rejected by the checker until implemented: `dom` with `def_order`/`load_order`/`scope`, and `output ... IMPLICIT/PERMUTATION/CONSTRAINTS`.

Known differences to VeriPB 3 and CakePB. PBLean rejects some proofs that VeriPB and CakePB accept: input constraints are used as written, not normalized; all `rup` hint ids are resolved before propagation, so an unknown id after the conflicting hint rejects the step; under strengthening-to-core, `red` database goals range over the whole database, while CakePB checks the core only (2 proofs of the VeriPB test suite); dominance, orders and scopes are not supported; an `obju` without `: subproof`, with a closing `qed : id`, or with an unproved non-trivial goal is rejected (VeriPB autoproves such goals, CakePB rejects them). An OPB objective without terms counts as absent, so `obji`/`eobj`/`obju` on it are rejected (both references accept). Output claims `output G FILE` are accepted without the output formula when the bound-side conditions hold (CakePB rejects `EQUISATISFIABLE`/`EQUIOPTIMAL` without the file); `sol : v` on an instance without objective is accepted with `v = 0` (CakePB; VeriPB rejects). PBLean accepts some proofs that VeriPB rejects, without losing soundness: a negative degree is clamped to 0, which gives a stronger constraint; and checked deletion under strengthening-to-core does not require an empty witness (CakePB accepts this too). Conclusions follow CakePB: an upper bound above the best solution value and `conclusion SAT`/`UNSAT` on an instance with an objective are accepted (VeriPB rejects them), and the lower bound of `conclusion BOUNDS` needs its hint `lb : id`, whose constraint must imply the bound even when the database contains a contradiction elsewhere (VeriPB searches the database). `conclusion UNSAT` after a logged solution is rejected, as by both references. `conclusion SAT : ;` is read as the all-false assignment, as CakePB does; VeriPB reads it as no hint (likewise an upper bound `ub : ;`).

In `veripb_reflect`, `rup C : hints` is checked by verified PB unit propagation as CakePB checks it: one pass over the hints in order, the negated target through an explicit `~`. The Expr-level `veripb_proof` path keeps its addition-based certificate.

## Application modules

Each module provides a trusted PB encoding and soundness theorems for a combinatorial problem. The `applications/` directory contains the corresponding OPB encodings and VeriPB kernel proofs, loaded at elaboration time. Naming convention: `Paley_97.opb` (encoding) and `Paley_97_kernel.pbp` (kernel proof).

**Independent set** (`IndependentSet.lean`) — Independence number of Paley graphs for all primes p ≡ 1 (mod 4) from 13 to 101. (Paley(5) is omitted as α(K₅) = 1 is trivial.)
```lean
theorem paley13_alpha  : independenceNumber (paley 13)  3
theorem paley17_alpha  : independenceNumber (paley 17)  3
theorem paley29_alpha  : independenceNumber (paley 29)  4
theorem paley37_alpha  : independenceNumber (paley 37)  4
theorem paley41_alpha  : independenceNumber (paley 41)  5
theorem paley53_alpha  : independenceNumber (paley 53)  5
theorem paley61_alpha  : independenceNumber (paley 61)  5
theorem paley73_alpha  : independenceNumber (paley 73)  5
theorem paley89_alpha  : independenceNumber (paley 89)  5
theorem paley97_alpha  : independenceNumber (paley 97)  6
theorem paley101_alpha : independenceNumber (paley 101) 5
```

The same eleven independence numbers are also proved from one *optimization* proof each (`independent_set_opt_reflect`, namespace `PaleyOptShowcase`): RoundingSat minimizes `-1 x1 ... -1 xp` over the edge constraints and its elaborated proof ends with `conclusion BOUNDS -k : id -k : solution`, which the bridge theorem `independenceNumber_of_bounds` turns into `independenceNumber (paley p) k`, both directions from a single certificate (the decision route above needs an UNSAT proof plus a witness checked by `native_decide`). All eleven take about 13 s together.

The data yields a formally verified non-monotonicity result: α(Paley(97)) = 6 > 5 = α(Paley(101)).
```lean
theorem paley_alpha_not_monotone :
    ∃ p q : Nat, p < q ∧ ∃ a b : Nat,
      independenceNumber (paley p) a ∧ independenceNumber (paley q) b ∧ a > b
```

**Langford pairing** (`Langford.lean`) — No Langford pairing of orders 6 and 9 exists.
```lean
-- Langford namespace
theorem langford6_impossible : ¬hasLangfordPairing 6
theorem langford9_impossible : ¬hasLangfordPairing 9
```

**Schur number** (`Schur.lean`) — S(2) = 4: {1,...,4} has a Schur-free 2-coloring but {1,...,5} does not. Generalized to k-coloring: S(3) = 13 verified via one-hot encoding.
```lean
-- Schur namespace
theorem schur_number_2 : schurNumber 4
theorem schur14_impossible : ¬hasKSchurFreeColoring 3 14
```

**Van der Waerden number** (`VanDerWaerden.lean`) — W(2,3) = 9: {1,...,8} has an AP-free 2-coloring but {1,...,9} does not. Generalized to k-term APs: W(2,4) = 35 verified.
```lean
-- VanDerWaerden namespace
theorem vdw_number_2_3 : vanDerWaerdenNumber 8
theorem vdw35_impossible : ¬hasKAPFreeColoring 4 35
```

**Ramsey number** (`Ramsey.lean`) — R(3,3) = 6: K₅ has a triangle-free 2-coloring but K₆ does not. Generalized to asymmetric R(s,t): R(3,4) ≤ 9 verified.
```lean
-- Ramsey namespace
theorem ramsey_3_3 : ramseyNumber 5
theorem ramsey9_34_impossible : ¬hasAsymRamseyFreeColoring 9 3 4
```

**Equitable coloring** (`EquitableColoring.lean`) — The equitable chromatic number of K_{3,3,1} is 5.
```lean
-- EquitableColoring namespace
theorem k331_eq_chromatic : equitableChromaticNumber k331 5
```

**Pigeonhole principle** (`Tests/Reflect.lean`, `applications/php/`) — PHP(3,2) is unsatisfiable. Exercises the `red` rule for symmetry breaking via a cyclic substitution witness.
```lean
theorem php32_red_reflect : formulaUnsat
```

**Bin packing** (`BinPacking.lean`) — 12 items of sizes [10,9,8,8,6,5,4,4,4,4,4,4] do not fit into 5 bins of capacity 14. The total size equals 5×14 = 70 (not refutable by weight alone); unsatisfiability follows from a rounding argument on the capacity constraints. The optimization form (`binpack_opt_reflect`, bin-use variables `y_j`, objective `min: Σ y_j`) proves that 6 bins are the minimum from one proof with 6 or with 7 bins available.
```lean
-- BinPacking namespace
theorem bp12_5_impossible : ¬hasPacking inst12_5
theorem bp12_m6_minBins : minBins inst12_m6 6
theorem bp12_m7_minBins : minBins inst12_m7 6
```

**Vertex cover** (`VertexCover.lean`) — Minimum vertex covers from one optimization proof each (`vertex_cover_reflect`): the Petersen graph needs 6 vertices, Paley(13), Paley(17) and Paley(29) need 10, 14 and 25.
```lean
-- VertexCoverShowcase namespace
theorem petersen_tau : vertexCoverNumber petersen 6
theorem paley13_tau  : vertexCoverNumber (paley 13) 10
theorem paley17_tau  : vertexCoverNumber (paley 17) 14
theorem paley29_tau  : vertexCoverNumber (paley 29) 25
```

**Chromatic number** (`Chromatic.lean`) — Colour-class variables with colour-use indicators, objective `min: Σ y_c` (`chromatic_reflect g k c` with `k` colours available): the Petersen graph has chromatic number 3 and the Grötzsch graph (Mycielski of C₅) has chromatic number 4.
```lean
-- ChromaticShowcase namespace
theorem petersen_chi  : chromaticNumber petersen 3
theorem groetzsch_chi : chromaticNumber groetzsch 4
```

**Predicate convention:** Each predicate `fooNumber n` asserts that `n` is the largest value for which the feasibility condition holds. For example, `ramseyNumber 5` means K₅ admits a Ramsey-free 2-coloring but K₆ does not, hence R(3,3) = 6.

## Trust base

Standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`) plus, per theorem, one native-evaluation axiom (`_native.<command>.ax_<n>`, the same mechanism `native_decide` uses) asserting that the compiled checker run returned `true`.

## Building

Requires [elan](https://github.com/leanprover/elan). The `lean-toolchain` file pins the exact Lean version.

```
lake build                 # build everything (~40 sec)
lake build VeriPBKernel    # build kernel + tests only (~20 sec)
```

The checker modules are precompiled to native code (`precompileModules`, like `bv_decide`), so all certificate checks — including the 11 Paley graph independence numbers in `IndependentSet.lean` — run compiled rather than interpreted.

## Benchmarks

`applications/benchmark.py` measures end-to-end verification times (one `veripb_reflect` command per instance, in a fresh `lean` process) for all showcase theorems; `applications/timing.lean` times the checker alone.
```
python3 applications/benchmark.py           # Lean verification times
python3 applications/benchmark.py --full    # Also re-solve + re-elaborate
```
The `--full` mode requires [RoundingSat](https://gitlab.com/MIAOresearch/software/roundingsat) and [VeriPB](https://gitlab.com/MIAOresearch/software/VeriPB) in PATH. Both scripts load the precompiled checker libraries; a plain `lake env lean` run does not, and then the checker executes in Lean's IR interpreter, about 20x slower.

Independence numbers of Paley graphs, v0.4.0 on an Apple M2 (Lean 4.30.0):

| p | proof lines | `checkProofBool` | of which parsing | `veripb_reflect` end-to-end |
|---|---|---|---|---|
| 53 | 1,848 | 28 ms | 8 ms | 0.97 s |
| 73 | 9,808 | 176 ms | 45 ms | 1.29 s |
| 89 | 36,795 | 787 ms | 174 ms | 2.06 s |
| 101 | 62,924 | 1.33 s | 0.29 s | 2.83 s |

The end-to-end time includes about 0.7 s of Lean startup and, for Paley(101), 0.6 s for compiling the auxiliary definition that `nativeEqTrue` evaluates (the constraint array as a Lean term). The native VeriPB checker verifies the Paley(101) proof in 0.23 s.

The paper reports 200 s for Paley(101) with v0.3.1. That figure was a benchmarking error: the script ran the checker in Lean's IR interpreter instead of the precompiled native code that `lake build` uses. Measured correctly, v0.3.1 took 9.3 s; v0.4.0 brings this to 2.8 s (checker 6.2 s to 1.3 s) through the array-based runtime checker and the byte-level parser. The paper's conclusion that PBLean is about 200x slower than VeriPB should read about 12x end-to-end, or 6x for the checker alone.

## References

- S. Szeider. *PBLean: Pseudo-Boolean Proof Certificates for Lean 4.* [arXiv:2602.08692](https://arxiv.org/abs/2602.08692), 2026.
- [VeriPB proof system](https://gitlab.com/MIAOresearch/software/VeriPB)
- B. Bogaerts, S. Gocht, C. McCreesh, J. Nordström. *Certified Symmetry and Dominance Breaking for Combinatorial Optimisation.* AAAI 2022.
- [RoundingSat PB solver](https://gitlab.com/MIAOresearch/software/roundingsat)

## License

Apache 2.0. See [LICENSE](LICENSE).
