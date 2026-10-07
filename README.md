# Artifact guide

This is the artifact accompanying the paper *Separating Parsing Expression
Grammars using Cell-Probe Lower Bounds*.

```
README.md          this guide
CITATION.cff       preferred citation metadata
.zenodo.json       Zenodo deposit metadata
LICENSE            Apache-2.0
lakefile.toml      Lake package
lake-manifest.json pinned mathlib commit
lean-toolchain     pinned Lean version
PegSeparation/     the development
```

## Build

```sh
lake exe cache get     # fetch dependencies and mathlib's compiled oleans
lake build             # build the default target
```

On an Apple M2 Max, `lake exe cache get` took about 15 minutes and `lake build`
about 4 minutes afterwards. The default target does **not** include the
independent lower-bound route; see below.

## Canonical entry points

```sh
lake env lean PegSeparation/CFLNotPEG/Main.lean   # about 13 s
lake env lean PegSeparation/Closure/Main.lean     # about 11 s
```

A third, optional entry point re-proves the cell-probe lower bound without
Ko's theorem. Its modules are not part of the default target, so it must be
built explicitly:

```sh
lake build PegSeparation.CFLNotPEG.InternalLowerBoundMain
lake env lean PegSeparation/CFLNotPEG/InternalLowerBoundMain.lean
```

## Paper results and their Lean declarations

| Paper result | Lean declaration |
|---|---|
| Thm 3.5 (transfer theorem) | `Reduction.GenericTransfer.genericTransferTheorem` |
| Prop 4.7, 4.12, 4.13 (linear CFG and explicit PEG for `C`) | `Witness.LanguageCFG.LinearGrammar.cfg_language_eq_C`, `Witness.DirectPEG.C_recognizedByTotalPEG` |
| Cor 4.4 (no fast multiphase structure) | `CFLNotPEG.ko2026MultiphaseIPLowerBound` |
| Thm 4.19, Cor 4.20 (main separation, reversal) | `CFLNotPEG.finalSeparation`, `Closure.reversalNonClosure` |
| Lem 5.2, 5.3, 5.7 (factorization, `Pref ∈ PEG`, star envelope) | `Closure.witness_factorization`, `Closure.pref_isPEG`, `Closure.cFirst_isSCA_degree_six_radius_two`, `Closure.starWitness_kstar_inter_shape` |
| Lem 5.4, Thm 5.6 (Boolean closure, `REG · PEG ⊆ PEG`) | `Closure.recognizedByTotalPEG_union`, `_inter`, `_compl`, `_of_isRegular`, `_mul_of_isRegular_left` |
| Thm 5.5, 5.8, Cor 5.9 (concatenation, star, homomorphism, substitution) | `Closure.concatenationNonClosure`, `Closure.kleeneStarNonClosure`, `Closure.HomomorphismInternal.homomorphismNonClosureInternal` |
| Thm 5.10 (inverse homomorphism) | `Closure.recognizedByTotalPEG_inverseImage` |
| Cor 5.11 (hardest CFL is not PEG) | `Closure.GreibachHardest.greibachHardest_isContextFree_not_totalPEG` |
