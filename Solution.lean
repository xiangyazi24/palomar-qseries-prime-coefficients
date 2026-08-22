import PalomarQseriesPrimeCoefficients.Public
import PalomarQseriesPrimeCoefficients

/-!
# Unconditional split-prime coefficients

The Solution-side public definitions are transported coordinatewise to the
extracted Paper 3 closure.  The registered proofs then combine the verified
finite-atom classification, uniform geometric normalization, and invariance
under signed powers of the fundamental unit.
-/

namespace PalomarQseriesPrimeCoefficients

noncomputable section

/-! ## Public-to-internal transport -/

private abbrev InternalPhi := QseriesFormalization.Ch10.PhiInt

private def toInternalPhi (x : PhiInt) : InternalPhi :=
  ⟨x.a, x.b⟩

private def fromInternalPhi (x : InternalPhi) : PhiInt :=
  ⟨x.a, x.b⟩

private theorem toInternal_fromInternal (x : InternalPhi) :
    toInternalPhi (fromInternalPhi x) = x := by
  cases x
  rfl

private theorem BCoeff_eq_internal (N : Nat) :
    BCoeff N = QseriesFormalization.Ch10.BCoeff N := by
  rfl

private theorem norm_eq_internal (x : PhiInt) :
    PhiInt.norm x = QseriesFormalization.Ch10.PhiInt.norm (toInternalPhi x) := by
  rfl

private theorem epsMul_eq_internal (x : PhiInt) :
    toInternalPhi (epsMul x) =
      QseriesFormalization.Ch10.epsMul (toInternalPhi x) := by
  rfl

private theorem epsInvMul_eq_internal (x : PhiInt) :
    toInternalPhi (epsInvMul x) =
      QseriesFormalization.Ch10.epsInvMul (toInternalPhi x) := by
  rfl

private theorem neg_eq_internal (x : PhiInt) :
    toInternalPhi (-x) = -(toInternalPhi x) := by
  rfl

private theorem epsNatMul_eq_internal (n : Nat) (x : PhiInt) :
    toInternalPhi (epsNatMul n x) =
      QseriesFormalization.Ch10.epsNatMul n (toInternalPhi x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [epsNatMul, QseriesFormalization.Ch10.epsNatMul,
        epsMul_eq_internal, ih]

private theorem epsInvNatMul_eq_internal (n : Nat) (x : PhiInt) :
    toInternalPhi (epsInvNatMul n x) =
      QseriesFormalization.Ch10.epsInvNatMul n (toInternalPhi x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [epsInvNatMul, QseriesFormalization.Ch10.epsInvNatMul,
        epsInvMul_eq_internal, ih]

private theorem epsZPowMul_eq_internal (m : Int) (x : PhiInt) :
    toInternalPhi (epsZPowMul m x) =
      QseriesFormalization.Ch10.epsZPowMul m (toInternalPhi x) := by
  cases m with
  | ofNat n => exact epsNatMul_eq_internal n x
  | negSucc n => exact epsInvNatMul_eq_internal (n + 1) x

private theorem sameWindowSign_iff_internal (x : PhiInt) :
    SameWindowSign x ↔
      QseriesFormalization.Ch10.SameWindowSign (toInternalPhi x) := by
  rfl

private def toInternalGeometric {x : PhiInt} (c : GeometricSectorCert x) :
    QseriesFormalization.Ch10.GeometricSectorCert (toInternalPhi x) where
  lift := c.lift
  normalized := by
    have h := (sameWindowSign_iff_internal
      (epsZPowMul (-c.lift) x)).mp c.normalized
    simpa only [epsZPowMul_eq_internal] using h

private theorem iotaCert_eq_internal {x : PhiInt}
    (c : GeometricSectorCert x) :
    iotaCert x c.toSectorCert =
      QseriesFormalization.Ch10.iotaCert (toInternalPhi x)
        (toInternalGeometric c).toSectorCert := by
  rfl

private theorem sameIdeal_to_internal {x y : PhiInt}
    (hxy : sameIdeal x y) :
    QseriesFormalization.Ch10.sameIdeal (toInternalPhi x) (toInternalPhi y) := by
  rcases hxy with ⟨m, negative, hxy⟩
  refine ⟨m, negative, ?_⟩
  cases negative with
  | false =>
      have h := congrArg toInternalPhi hxy
      simpa only [epsZPowMul_eq_internal] using h
  | true =>
      have h := congrArg toInternalPhi hxy
      simpa only [neg_eq_internal, epsZPowMul_eq_internal] using h

private def fromInternalGeometric {x : InternalPhi}
    (c : QseriesFormalization.Ch10.GeometricSectorCert x) :
    GeometricSectorCert (fromInternalPhi x) where
  lift := c.lift
  normalized := by
    have hmap :
        toInternalPhi
            (epsZPowMul (-c.lift) (fromInternalPhi x)) =
          QseriesFormalization.Ch10.epsZPowMul (-c.lift) x := by
      rw [epsZPowMul_eq_internal, toInternal_fromInternal]
    apply (sameWindowSign_iff_internal _).mpr
    rw [hmap]
    exact c.normalized

/-! ## Registered proofs -/

/-- The closed witness is evaluated in the exact extracted coefficient model. -/
theorem BCoeff_not_multiplicative_witness :
    BCoeff 34 ≠ BCoeff 1 * BCoeff 3 := by
  simpa only [BCoeff_eq_internal] using
    QseriesFormalization.Ch10.BCoeff_not_multiplicative_witness

private theorem prime_BCoeff_iota_for_public_generator
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (c : GeometricSectorCert x) :
    (BCoeff ((p - 1) / 10)).natAbs = 2 ↔
      iotaCert x c.toSectorCert = 1 := by
  have hnormInternal :
      QseriesFormalization.Ch10.PhiInt.norm (toInternalPhi x) =
        -(p : Int) := by
    simpa only [← norm_eq_internal] using hnorm
  simpa only [BCoeff_eq_internal, iotaCert_eq_internal] using
    QseriesFormalization.Ch10.prime_BCoeff_natAbs_eq_two_iff_iota_one_unconditional
      hp hp10 hnormInternal (toInternalGeometric c)

/-- The complete classification combines the four-value theorem with
generator existence and the certificate-uniform magnitude/iota criterion. -/
theorem prime_BCoeff_complete_classification
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1) :
    BCoeff ((p - 1) / 10) ∈ ({-2, -1, 1, 2} : Set Int) ∧
    (∃ x : PhiInt, PhiInt.norm x = -(p : Int)) ∧
    ∀ {x : PhiInt}, PhiInt.norm x = -(p : Int) →
      Nonempty (GeometricSectorCert x) ∧
      ∀ c : GeometricSectorCert x,
        (BCoeff ((p - 1) / 10)).natAbs = 2 ↔
          iotaCert x c.toSectorCert = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [BCoeff_eq_internal] using
      QseriesFormalization.Ch10.prime_BCoeff_four_values_unconditional hp hp10
  · rcases QseriesFormalization.Ch10.exists_negNormPrimeGenerator hp hp10 with
      ⟨x, hnorm⟩
    refine ⟨fromInternalPhi x, ?_⟩
    simpa [fromInternalPhi, QseriesFormalization.Ch10.PhiInt.norm] using hnorm
  · intro x hnorm
    have hnormInternal :
        QseriesFormalization.Ch10.PhiInt.norm (toInternalPhi x) =
          -(p : Int) := by
      simpa only [← norm_eq_internal] using hnorm
    rcases QseriesFormalization.Ch10.exists_geometricSectorCert
        hp hp10 hnormInternal with ⟨cInternal⟩
    refine ⟨⟨fromInternalGeometric cInternal⟩, ?_⟩
    intro c
    exact prime_BCoeff_iota_for_public_generator hp hp10 hnorm c

/-- Unit-orbit invariance follows by transporting both certificates and the
signed-power relation to the internal geometric theorem. -/
theorem geometric_iota_eq_of_sameIdeal
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x y : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (hxy : sameIdeal x y)
    (c : GeometricSectorCert x) (d : GeometricSectorCert y) :
    iotaCert y d.toSectorCert = iotaCert x c.toSectorCert := by
  have hnormInternal :
      QseriesFormalization.Ch10.PhiInt.norm (toInternalPhi x) =
        -(p : Int) := by
    simpa only [← norm_eq_internal] using hnorm
  have h := QseriesFormalization.Ch10.geometric_iota_eq_of_sameIdeal
    hp hp10 hnormInternal (sameIdeal_to_internal hxy)
      (toInternalGeometric c) (toInternalGeometric d)
  simpa only [iotaCert_eq_internal] using h

end
end PalomarQseriesPrimeCoefficients
