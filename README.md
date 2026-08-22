# Prime coefficients of a nonmultiplicative indefinite theta series

This is the standalone public Lean 4 package for Xiang Huang's paper
*Prime magnitudes and nonvanishing for a nonmultiplicative indefinite theta
series over Q(sqrt(5))*.

For the coefficient sequence `BCoeff` defined as the difference of two signed
cone sums for the norm form over `Z[phi]`, the formalization proves:

- the closed nonmultiplicativity witness
  `BCoeff 34 != BCoeff 1 * BCoeff 3`;
- for every rational prime `p` congruent to `1` modulo `10`, the coefficient
  `BCoeff ((p - 1) / 10)` belongs to `{-2, -1, 1, 2}`;
- every such prime has a golden integer of norm `-p`, and every norm-`-p`
  generator has a strict integral fundamental-window normalization;
- for every normalized generator, the coefficient has magnitude two exactly
  when the geometric residue invariant `iota` is one modulo three;
- this geometric invariant is unchanged under the explicitly defined signed
  fundamental-unit orbit `y = +/- eps^m x`.

The proof constructs the norm-negative generator, classifies the norm-one
units, normalizes the real embeddings by integral descent, partitions the
finite cone atoms into two distinct conjugate classes, counts them exactly,
and proves their signed weights agree when both classes contribute. Thus the
prime theorem is not conditional on a supplied per-prime certificate.

The accompanying paper additionally derives relative densities `1/3` and
`2/3` for coefficient magnitudes two and one from a specialized
Hecke--Mitsui thin-cone prime theorem. That external analytic input and the
paper's computational comparison with Chan's q-series kernel are not among the
Lean declarations registered here.

## Registered statement surface

`Challenge.lean` imports only Mathlib and is 192 lines. It contains the public
definitions and three theorem statements selected by `comparator.json`:

- `PalomarQseriesPrimeCoefficients.BCoeff_not_multiplicative_witness`;
- `PalomarQseriesPrimeCoefficients.prime_BCoeff_complete_classification`;
- `PalomarQseriesPrimeCoefficients.geometric_iota_eq_of_sameIdeal`.

The name `sameIdeal` is local terminology for the displayed relation
`y = +/- eps^m x`; the registered theorem does not identify that relation with
Mathlib's `Associated` predicate or with equality of principal ideals.

Palomar does not allow project-local source in the Challenge import closure.
The marked public-definition block is therefore inline in `Challenge.lean` and
duplicated byte-for-byte in the Solution-side
`PalomarQseriesPrimeCoefficients/Public.lean`. The repository's drift check
fails unless those two blocks are exactly equal.

## Repository map

- `Challenge.lean`: Mathlib-only definitions and the three statement holes.
- `Solution.lean`: transports and proofs from the extracted development.
- `PalomarQseriesPrimeCoefficients/Public.lean`: Solution-side copy of the
  public statement definitions.
- `QseriesFormalization/`: the 28-file transitive proof closure extracted from
  the private canonical repository `xiangyazi24/Q-series-and-Chan-s-work` at
  commit
  `95573179f143e85dfc551d896fe9be6ca472250e`.
- `paper/`: signed TeX source, bibliography, compiled 16-page PDF, and the
  dependency-free script reproducing the aggregate finite computations.
- `comparator.json`: the three compared declarations and permitted axioms.
- `formalization.yaml`: scope, provenance, automation, fidelity, and review.

This repository is the substantive, self-contained public source for the
Palomar entry; the private development is not a build dependency.

## Verification

Run the full checks on Linux:

```text
lake exe cache get
lake build
lake env lean AxiomAudit.lean
python3 paper/numerical_audit.py
./scripts/verify-public-surface.sh
ruby scripts/validate-formalization.rb
./test/landrun_wrapper_test.sh
ruby test/validate_formalization_test.rb
./scripts/verify-comparator.sh
```

The final command runs pinned Comparator, Lean's kernel export, NanoDa replay,
and the Landrun policy wrapper. Palomar independently forces NanoDa during its
own verification.

After a public commit is frozen and checked, its full SHA can be sent through
[Palomar's submission service](https://submit.palomar-registry.org/).
