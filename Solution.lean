import PalomarQseriesPrimeCoefficients.Public
import PalomarQseriesPrimeCoefficients

/-!
# Nonmultiplicativity and conditional prime coefficients

This file converts the shared public certificate records explicitly to the
extracted internal types and applies the two verified internal endpoints.
-/

namespace PalomarQseriesPrimeCoefficients

noncomputable section

/-! ## Explicit public-to-internal transport -/

private def toInternalPhi (x : PhiInt) :
    QseriesFormalization.Ch10.PhiInt :=
  ⟨x.a, x.b⟩

private theorem BCoeff_eq_internal (N : Nat) :
    BCoeff N = QseriesFormalization.Ch10.BCoeff N := by
  rfl

private theorem AAtoms_eq_internal (N : Nat) :
    AAtoms N = QseriesFormalization.Ch10.AAtoms N := by
  rfl

private theorem DAtoms_eq_internal (N : Nat) :
    DAtoms N = QseriesFormalization.Ch10.DAtoms N := by
  rfl

private theorem AAtomWeight_eq_internal (q : Nat × Nat) :
    AAtomWeight q = QseriesFormalization.Ch10.AAtomWeight q := by
  rfl

private theorem DAtomWeight_eq_internal (q : Nat × Nat) :
    DAtomWeight q = QseriesFormalization.Ch10.DAtomWeight q := by
  rfl

private theorem atomCount_eq_internal (N : Nat) :
    atomCount N = QseriesFormalization.Ch10.atomCount N := by
  rfl

private def toInternalSector {x : PhiInt} (c : SectorCert x) :
    QseriesFormalization.Ch10.SectorCert (toInternalPhi x) where
  δ := c.δ

private theorem contributes_iff_internal (x : PhiInt) (c : SectorCert x) :
    Contributes x c ↔
      QseriesFormalization.Ch10.Contributes
        (toInternalPhi x) (toInternalSector c) := by
  rfl

private theorem reflected_contributes_iff_internal
    (x : PhiInt) (c : SectorCert x) :
    Contributes (PhiInt.star x) (reflectedSectorCert x c) ↔
      QseriesFormalization.Ch10.Contributes
        (QseriesFormalization.Ch10.PhiInt.star (toInternalPhi x))
        (QseriesFormalization.Ch10.reflectedSectorCert
          (toInternalPhi x) (toInternalSector c)) := by
  rfl

private def toInternalSplit {p : Nat} (sp : SplitPrimeCert p) :
    QseriesFormalization.Ch10.SplitPrimeCert p where
  π := toInternalPhi sp.π
  hp := sp.hp
  hp10 := sp.hp10
  hnorm := by
    simpa [toInternalPhi, PhiInt.norm,
      QseriesFormalization.Ch10.PhiInt.norm] using sp.hnorm
  hmod2 := by
    simpa [toInternalPhi, toF4,
      QseriesFormalization.Ch10.toF4] using sp.hmod2

private def toInternalAtoms {p : Nat} (sp : SplitPrimeCert p)
    (c : SectorCert sp.π) (atoms : PrimeAtomCertificate sp c) :
    QseriesFormalization.Ch10.PrimeAtomCertificate
      (toInternalSplit sp) (toInternalSector c) where
  sign := atoms.sign
  all_A := by
    intro q hq
    have hqPublic : q ∈ AAtoms ((p - 1) / 10) := by
      simpa only [AAtoms_eq_internal] using hq
    simpa only [AAtomWeight_eq_internal] using atoms.all_A q hqPublic
  all_D := by
    intro q hq
    have hqPublic : q ∈ DAtoms ((p - 1) / 10) := by
      simpa only [DAtoms_eq_internal] using hq
    simpa only [DAtomWeight_eq_internal] using atoms.all_D q hqPublic
  one_atom_bound := by
    simpa only [atomCount_eq_internal] using atoms.one_atom_bound
  atom_of_left_contributes := by
    intro h
    have hPublic : Contributes sp.π c :=
      (contributes_iff_internal sp.π c).mpr h
    simpa only [atomCount_eq_internal] using
      atoms.atom_of_left_contributes hPublic
  atom_of_right_contributes := by
    intro h
    have hPublic :
        Contributes (PhiInt.star sp.π) (reflectedSectorCert sp.π c) :=
      (reflected_contributes_iff_internal sp.π c).mpr h
    simpa only [atomCount_eq_internal] using
      atoms.atom_of_right_contributes hPublic

/-! ## Registered theorems -/

/-- A closed nonmultiplicativity witness for the actual coefficient function. -/
theorem BCoeff_not_multiplicative_witness :
    BCoeff 34 ≠ BCoeff 1 * BCoeff 3 := by
  simpa only [BCoeff_eq_internal] using
    QseriesFormalization.Ch10.BCoeff_not_multiplicative_witness

/--
Conditional four-valued classification from an explicit split-prime,
sector-label, and finite atom certificate.
-/
theorem prime_coeff_classification {p : Nat} (sp : SplitPrimeCert p)
    (c : SectorCert sp.π) (atoms : PrimeAtomCertificate sp c) :
    BCoeff ((p - 1) / 10) ∈ ({-2, -1, 1, 2} : Set Int) := by
  simpa only [BCoeff_eq_internal] using
    QseriesFormalization.Ch10.prime_coeff_classification
      (toInternalSplit sp) (toInternalSector c) (toInternalAtoms sp c atoms)

end
end PalomarQseriesPrimeCoefficients
