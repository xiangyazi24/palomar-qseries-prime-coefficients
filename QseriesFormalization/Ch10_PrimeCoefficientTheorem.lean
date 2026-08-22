import QseriesFormalization.Ch10_PrimeSignCoherence
import QseriesFormalization.Ch10_PrimeIdealInvariant
import Mathlib.Tactic

/-!
# Ch10: Unconditional finite prime-coefficient theorem

Class coverage and one-atom uniqueness reduce every finite atom to the unique
atom in one of the two conjugate classes.  The both-good coordinate theorem
shows that those two atoms have equal full `BWeight`.  Hence every atom at a
split-prime level has one common sign in `{+1,-1}`, so the absolute coefficient
is exactly the atom count.
-/

namespace QseriesFormalization
namespace Ch10

theorem finiteAtom_common_sign_at_prime
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (c : GeometricSectorCert x)
    (o : OrientedSectorNormalization (p := p) x c)
    (ostar : OrientedSectorNormalization (p := p)
      (PhiInt.star x) c.reflected) :
    ∃ s : Int, (s = 1 ∨ s = -1) ∧
      ∀ a : PrimeFinAtom ((p - 1) / 10), a.weight = s := by
  by_cases hleft : Contributes x c.toSectorCert
  · rcases exists_primeClassAtom_of_contributes hp hp10 hnorm c o hleft with
      ⟨left⟩
    have hsign := PrimeFinAtom.weight_eq_one_or_neg_one left.atom
    by_cases hright :
        Contributes (PhiInt.star x) c.reflected.toSectorCert
    · rcases exists_primeClassAtom_of_contributes hp hp10
          (by rw [PhiInt.norm_star, hnorm]) c.reflected ostar hright with
        ⟨right⟩
      have hweights := both_good_atom_weights_eq hp hp10 hnorm c o
        hleft hright left right
      refine ⟨left.atom.weight, hsign, ?_⟩
      intro a
      rcases a.class_cover hp hp10 hnorm with ha | ha
      · have heq : a = left.atom := (left.atom_eq ⟨a, ha⟩).symm
        rw [heq]
      · have heq : a = right.atom := (right.atom_eq ⟨a, ha⟩).symm
        rw [heq]
        exact hweights.symm
    · refine ⟨left.atom.weight, hsign, ?_⟩
      intro a
      rcases a.class_cover hp hp10 hnorm with ha | ha
      · have heq : a = left.atom := (left.atom_eq ⟨a, ha⟩).symm
        rw [heq]
      · exfalso
        apply hright
        exact contributes_of_primeClassAtom hp hp10
          (by rw [PhiInt.norm_star, hnorm]) c.reflected ostar ⟨a, ha⟩
  · have hright :
        Contributes (PhiInt.star x) c.reflected.toSectorCert := by
      rcases geometric_at_least_one_contributes hp hp10 hnorm c with h | h
      · exact (hleft h).elim
      · exact h
    rcases exists_primeClassAtom_of_contributes hp hp10
        (by rw [PhiInt.norm_star, hnorm]) c.reflected ostar hright with
      ⟨right⟩
    have hsign := PrimeFinAtom.weight_eq_one_or_neg_one right.atom
    refine ⟨right.atom.weight, hsign, ?_⟩
    intro a
    rcases a.class_cover hp hp10 hnorm with ha | ha
    · exfalso
      apply hleft
      exact contributes_of_primeClassAtom hp hp10 hnorm c o ⟨a, ha⟩
    · have heq : a = right.atom := (right.atom_eq ⟨a, ha⟩).symm
      rw [heq]

/-- At a split-prime level, cancellation is impossible: coefficient magnitude
equals the exact number of finite atoms. -/
theorem BCoeff_natAbs_eq_atomCount_at_prime
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (c : GeometricSectorCert x)
    (o : OrientedSectorNormalization (p := p) x c)
    (ostar : OrientedSectorNormalization (p := p)
      (PhiInt.star x) c.reflected) :
    (BCoeff ((p - 1) / 10)).natAbs = atomCount ((p - 1) / 10) := by
  rcases finiteAtom_common_sign_at_prime hp hp10 hnorm c o ostar with
    ⟨s, hs, hall⟩
  have hA : ∀ q ∈ AAtoms ((p - 1) / 10), AAtomWeight q = s := by
    intro q hq
    have h := hall
      (Sum.inl (⟨q, hq⟩ : ↑(AAtoms ((p - 1) / 10))) :
        PrimeFinAtom ((p - 1) / 10))
    simpa [PrimeFinAtom.weight] using h
  have hD : ∀ q ∈ DAtoms ((p - 1) / 10), DAtomWeight q = s := by
    intro q hq
    have h := hall
      (Sum.inr (⟨q, hq⟩ : ↑(DAtoms ((p - 1) / 10))) :
        PrimeFinAtom ((p - 1) / 10))
    simpa [PrimeFinAtom.weight] using h
  have hcoeff := BCoeff_eq_signed_atom_count ((p - 1) / 10) s hA hD
  rw [hcoeff]
  rcases hs with rfl | rfl <;> simp

theorem prime_BCoeff_natAbs_eq_two_iff_iota_one
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (c : GeometricSectorCert x)
    (o : OrientedSectorNormalization (p := p) x c)
    (ostar : OrientedSectorNormalization (p := p)
      (PhiInt.star x) c.reflected) :
    (BCoeff ((p - 1) / 10)).natAbs = 2 ↔
      iotaCert x c.toSectorCert = 1 := by
  rw [BCoeff_natAbs_eq_atomCount_at_prime hp hp10 hnorm c o ostar]
  exact atomCount_eq_two_iff_iota_eq_one hp hp10 hnorm c o ostar

/-- Prime magnitude classification for any norm-negative generator and its
geometric normalization.  The two mod-five orientations are constructed
internally, so they are not premises of the public theorem. -/
theorem prime_BCoeff_natAbs_eq_two_iff_iota_one_unconditional
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (c : GeometricSectorCert x) :
    (BCoeff ((p - 1) / 10)).natAbs = 2 ↔
      iotaCert x c.toSectorCert = 1 := by
  rcases exists_orientedSectorNormalization hp10 hnorm c with ⟨o⟩
  have hstar_norm : PhiInt.norm (PhiInt.star x) = -(p : Int) := by
    rw [PhiInt.norm_star, hnorm]
  rcases exists_orientedSectorNormalization hp10 hstar_norm c.reflected with
    ⟨ostar⟩
  exact prime_BCoeff_natAbs_eq_two_iff_iota_one hp hp10 hnorm c o ostar

theorem atomCount_eq_one_or_two_at_prime
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (c : GeometricSectorCert x)
    (o : OrientedSectorNormalization (p := p) x c)
    (ostar : OrientedSectorNormalization (p := p)
      (PhiInt.star x) c.reflected) :
    atomCount ((p - 1) / 10) = 1 ∨
      atomCount ((p - 1) / 10) = 2 := by
  rw [atomCount_eq_contributes_indicators hp hp10 hnorm c o ostar]
  by_cases hleft : Contributes x c.toSectorCert
  · by_cases hright :
        Contributes (PhiInt.star x) c.reflected.toSectorCert
    · simp [hleft, hright]
    · simp [hleft, hright]
  · have hright :
        Contributes (PhiInt.star x) c.reflected.toSectorCert := by
      rcases geometric_at_least_one_contributes hp hp10 hnorm c with h | h
      · exact (hleft h).elim
      · exact h
    simp [hleft, hright]

theorem prime_BCoeff_ne_zero
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (c : GeometricSectorCert x)
    (o : OrientedSectorNormalization (p := p) x c)
    (ostar : OrientedSectorNormalization (p := p)
      (PhiInt.star x) c.reflected) :
    BCoeff ((p - 1) / 10) ≠ 0 := by
  have hmag := BCoeff_natAbs_eq_atomCount_at_prime hp hp10 hnorm c o ostar
  rcases atomCount_eq_one_or_two_at_prime hp hp10 hnorm c o ostar with h | h
  · rw [h] at hmag
    exact (Int.natAbs_ne_zero.mp (by omega))
  · rw [h] at hmag
    exact (Int.natAbs_ne_zero.mp (by omega))

theorem prime_BCoeff_four_values
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (c : GeometricSectorCert x)
    (o : OrientedSectorNormalization (p := p) x c)
    (ostar : OrientedSectorNormalization (p := p)
      (PhiInt.star x) c.reflected) :
    BCoeff ((p - 1) / 10) ∈ ({-2, -1, 1, 2} : Set Int) := by
  have hmag := BCoeff_natAbs_eq_atomCount_at_prime hp hp10 hnorm c o ostar
  have hcount := atomCount_eq_one_or_two_at_prime hp hp10 hnorm c o ostar
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hcount with hcount | hcount
  · rw [hcount] at hmag
    rcases Int.natAbs_eq_iff.mp hmag with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
  · rw [hcount] at hmag
    rcases Int.natAbs_eq_iff.mp hmag with h | h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inl h

/-- Certificate-free nonvanishing for every rational prime congruent to one
modulo ten.  All generator and normalization data are constructed internally.
-/
theorem prime_BCoeff_ne_zero_unconditional
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1) :
    BCoeff ((p - 1) / 10) ≠ 0 := by
  rcases exists_negNormPrimeGenerator hp hp10 with ⟨x, hnorm⟩
  rcases exists_geometricSectorCert hp hp10 hnorm with ⟨c⟩
  rcases exists_orientedSectorNormalization hp10 hnorm c with ⟨o⟩
  have hstar_norm : PhiInt.norm (PhiInt.star x) = -(p : Int) := by
    rw [PhiInt.norm_star, hnorm]
  rcases exists_orientedSectorNormalization hp10 hstar_norm c.reflected with
    ⟨ostar⟩
  exact prime_BCoeff_ne_zero hp hp10 hnorm c o ostar

theorem prime_BCoeff_four_values_unconditional
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1) :
    BCoeff ((p - 1) / 10) ∈ ({-2, -1, 1, 2} : Set Int) := by
  rcases exists_negNormPrimeGenerator hp hp10 with ⟨x, hnorm⟩
  rcases exists_geometricSectorCert hp hp10 hnorm with ⟨c⟩
  rcases exists_orientedSectorNormalization hp10 hnorm c with ⟨o⟩
  have hstar_norm : PhiInt.norm (PhiInt.star x) = -(p : Int) := by
    rw [PhiInt.norm_star, hnorm]
  rcases exists_orientedSectorNormalization hp10 hstar_norm c.reflected with
    ⟨ostar⟩
  exact prime_BCoeff_four_values hp hp10 hnorm c o ostar

/-- Certificate-free existence of a geometric iota classification realizing
the coefficient-magnitude theorem for every admissible rational prime. -/
theorem exists_prime_BCoeff_iota_classification
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1) :
    ∃ (x : PhiInt) (c : GeometricSectorCert x),
      PhiInt.norm x = -(p : Int) ∧
      ((BCoeff ((p - 1) / 10)).natAbs = 2 ↔
        iotaCert x c.toSectorCert = 1) := by
  rcases exists_negNormPrimeGenerator hp hp10 with ⟨x, hnorm⟩
  rcases exists_geometricSectorCert hp hp10 hnorm with ⟨c⟩
  exact ⟨x, c, hnorm,
    prime_BCoeff_natAbs_eq_two_iff_iota_one_unconditional hp hp10 hnorm c⟩

end Ch10
end QseriesFormalization
