import PalomarQseriesPrimeCoefficients.Public

/-!
# Nonmultiplicativity and conditional prime coefficients

The imported public surface is Mathlib-only and makes the complete finite
coefficient and certificate burden of the two registered results explicit.
-/

namespace PalomarQseriesPrimeCoefficients

noncomputable section

/-! ## Registered theorems -/

/-- A closed nonmultiplicativity witness for the actual coefficient function. -/
theorem BCoeff_not_multiplicative_witness :
    BCoeff 34 ≠ BCoeff 1 * BCoeff 3 := by
  sorry

/--
Conditional four-valued classification from an explicit split-prime,
sector-label, and finite atom certificate.
-/
theorem prime_coeff_classification {p : Nat} (sp : SplitPrimeCert p)
    (c : SectorCert sp.π) (atoms : PrimeAtomCertificate sp c) :
    BCoeff ((p - 1) / 10) ∈ ({-2, -1, 1, 2} : Set Int) := by
  sorry

end
end PalomarQseriesPrimeCoefficients
