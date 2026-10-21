# PegSeparation, axiom-free

This repository is a fork of the Lean artifact of Jungyeom Kim and Jihyeok Park,
*Separating Parsing Expression Grammars using Cell-Probe Lower Bounds*
([arXiv:2608.29592](https://arxiv.org/abs/2608.29592); artifact v0.1.0,
[doi:10.5281/zenodo.22099762](https://doi.org/10.5281/zenodo.22099762)).
The mathematics is theirs. This fork only removes the three axioms that the artifact postulates,
so that the main separation and its Greibach corollary are checked in Lean with nothing beyond
the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## What is checked

`GreibachNoAxioms.lean` (at the root) states and proves:

```lean
-- Theorem 4.19: the witness is context-free and has no total PEG.
theorem PegSeparation.CFLNotPEG.fullyInternalSeparation :
    Language.IsContextFree WitnessLanguage ∧ ¬ RecognizedByTotalPEG WitnessLanguage

-- Corollary 5.11: Greibach's hardest context-free language has no total PEG.
theorem PegSeparation.Closure.GreibachHardest.greibachHardest_not_totalPEG_noAxioms :
    greibachWitness.language.IsContextFree ∧ ¬ greibachWitness.IsTotalPEG
```

and `#print axioms` reports only `[propext, Classical.choice, Quot.sound]` for both.

## The three axioms of the artifact, and what replaces them

| Axiom in the artifact | Replaced by |
|---|---|
| `External.Ko2026.multiphaseIPLowerBound` (Ko's lower bound, Thm 4.2) | the artifact's own optional route `CFLNotPEG.internalMultiphaseIPLowerBound` (via Larsen–Yu), together with `CFLNotPEG.loffForwardRepaired` for the PEG–SCA statement. Combining them is `fullyInternalSeparation`; no new proof was needed. |
| `External.Greibach1973.hardestContextFreeLanguage` (Greibach's theorem) | a proof: `Closure.GreibachProof.greibachWitness`, with `greibachWitness_nonerasing` recording that the homomorphisms never erase. |
| `External.BirmanUllman1973.recognizedByTotalPEG_inverseImage` (inverse images, possibly erasing) | for nonerasing homomorphisms, which is all that Greibach's construction needs: `Closure.recognizedByTotalPEG_inverseImage_nonerasing`. The general (erasing) statement is not proved here. |

`greibachHardest_not_totalPEG_noAxioms` then argues as Corollary 5.11 does: if the hardest language had a total
PEG, so would it without `ε`, hence so would the witness, which is a nonerasing inverse image of one of them.

## New files

- `GreibachNoAxioms.lean`: the two theorems above.
- `PegSeparation/Closure/InverseImageNonerasing*.lean` (4 files): the inverse-image closure. The simulating grammar
  has one rule per (subexpression, start offset in the current letter's block, end offset), with ordered choice over
  the finitely many end offsets; it is total when the original grammar is.
- `PegSeparation/Closure/GreibachProof*.lean` (19 files): Greibach's theorem. The proof of `L0`'s context-freeness,
  the conversion to Greibach standard form (ε-removal, unit removal, a left-corner construction, a fresh start) and
  the hardest-language theorem for standard-form grammars are copied, unchanged except for namespaces, from a
  core-Lean development over characters (`GreibachProof{Syntax,Semantics,Defs,CFLYmid,CFL,GNF*,Std*}`), which follows
  Nipkow's Isabelle formalization (AFP `Greibach_Hardest`). `GreibachProofToMathlib`, `GreibachProofOfMathlib`
  and `GreibachProofMain` translate between those grammars and mathlib's `ContextFreeGrammar` over a finite alphabet
  and build `greibachWitness`.

No file of the original artifact was changed.

## Checking

```sh
lake exe cache get
lake build PegSeparation.CFLNotPEG.InternalLowerBoundMain PegSeparation.Closure.GreibachProofMain \
  PegSeparation.Closure.InverseImageNonerasing
lake env lean GreibachNoAxioms.lean   # prints the axioms of both theorems
```

The new modules are not part of the default target.

## Scope

- The result is about total PEGs (`RecognizedByTotalPEG`, grammars that terminate on every input), as in the paper.
- The inverse-image closure is proved only for nonerasing homomorphisms.

## License

Apache-2.0, as the original artifact (see `LICENSE`). The original files are unchanged; the files listed under
"New files" are additions.

---

## 日本語の要約

Kim–Park の成果物から、公理として置かれていた三つ（Ko の下界、Greibach の定理、Birman–Ullman の逆像の閉包）を外したもの。
数学の結果は Kim–Park のもので、ここで足したのは機械検証だけ。主分離（定理 4.19）と系 5.11（Greibach の最難 CFL は全域な
PEG を持たない）が、標準の 3 公理だけで Lean で通る。Ko の下界は成果物自身の Larsen–Yu 経由の証明に差し替え、Greibach の定理と
（消去しない）逆像の閉包は新しく証明した。

---

# Original artifact guide

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
