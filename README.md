# Q-series prime coefficients

This repository prepares a
[Palomar](https://palomar-registry.org/) entry associated with
*Prime magnitudes and nonvanishing for a nonmultiplicative indefinite theta
series over Q(sqrt(5))* by Xiang Huang.

The repository is self-contained apart from its pinned Mathlib dependency. It
contains the fifteen-file transitive proof closure extracted from the canonical
internal development at commit
`4c926778c1b8701e3b4d85ec44c33766da9f724b`, together with the signed paper
snapshot in `paper/`.

## Registered statement surface

`PalomarQseriesPrimeCoefficients/Public.lean` defines the Mathlib-only public
surface, and `Challenge.lean` states two results over it:

- `BCoeff_not_multiplicative_witness` is the unconditional closed theorem
  `BCoeff 34 != BCoeff 1 * BCoeff 3` for the explicitly defined coefficient
  function;
- `prime_coeff_classification` is a conditional finite certificate consumer.
  Given a `SplitPrimeCert`, a `SectorCert` label, and a
  `PrimeAtomCertificate` carrying sign coherence, the two-atom bound, and both
  contribution-to-existence implications, it proves that the corresponding
  coefficient belongs to `{-2, -1, 1, 2}`.

The certificate burden is deliberately visible in the Challenge. In
particular, `SectorCert` contains only a `ZMod 3` label and does not certify
geometric sector membership. The formalization does not uniformly construct
these certificates for primes, prove the paper's sharper magnitude/iota
equivalence through this endpoint, formalize the Hecke--Mitsui density
argument, or identify this independently defined cone series with an older
Chan-project source object. The redundant nonzero corollary is proved in the
internal closure but is not a separate registered target.

## Repository map

- `PalomarQseriesPrimeCoefficients/Public.lean`: shared Mathlib-only
  coefficient and certificate surface.
- `Challenge.lean`: the two public theorem statements over that surface.
- `Solution.lean`: explicit type transports and proofs from the extracted
  closure.
- `QseriesFormalization/`: the fifteen-file substantive proof closure.
- `paper/`: signed TeX source, bibliography, and compiled PDF.
- `comparator.json`: declarations, definitions, and permitted axioms checked
  by Comparator.
- `formalization.yaml`: scope, provenance, automation, fidelity, and review.

This standalone repository and its fixed commit will be the authoritative
public source for the Palomar entry; the internal development is not a build
dependency.

## Verification

Run the full checks on Linux:

```text
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
./test/landrun_wrapper_test.sh
./test/validate_formalization_test.rb
./scripts/verify-comparator.sh
```

After the repository is publicly frozen, its exact commit can be sent through
[Palomar's submission form](https://submit.palomar-registry.org/).
