import QseriesFormalization.Ch10_PrimeClassDistinct
import Mathlib.Tactic

/-!
# Ch10: Exact atom count at split primes

Every finite atom belongs to one of the two conjugate unit classes.  The
bidirectional class bridge says that a bad class contains no atoms, while
one-atom uniqueness says that a good class contains exactly one.  Since the
two prime classes are distinct, the finite atom universe is therefore a
singleton or a two-point set, with cardinality given by the two contribution
indicators.
-/

namespace QseriesFormalization
namespace Ch10

instance instDecidableContributes (x : PhiInt) (c : SectorCert x) :
    Decidable (Contributes x c) := by
  unfold Contributes
  infer_instance

theorem geometric_iota_reflection
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (c : GeometricSectorCert x) :
    iotaCert (PhiInt.star x) c.reflected.toSectorCert =
      -iotaCert x c.toSectorCert - 1 := by
  have hx : toF4 x ≠ (0, 0) :=
    split_prime_mod2_nonzero hp hp10 (Or.inr hnorm)
  rw [c.toSectorCert_reflected]
  exact iota_reflection x c.toSectorCert hx

theorem both_contribute_iff_iota_eq_one
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (c : GeometricSectorCert x) :
    (Contributes x c.toSectorCert ∧
      Contributes (PhiInt.star x) c.reflected.toSectorCert) ↔
      iotaCert x c.toSectorCert = 1 := by
  have href := geometric_iota_reflection hp hp10 hnorm c
  unfold Contributes
  rw [href]
  have hfinite : ∀ i : ZMod 3,
      (i ≠ 2 ∧ -i - 1 ≠ 2) ↔ i = 1 := by decide
  exact hfinite (iotaCert x c.toSectorCert)

theorem PrimeFinAtom.eq_left_or_right
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (left : PrimeClassAtom x ((p - 1) / 10))
    (right : PrimeClassAtom (PhiInt.star x) ((p - 1) / 10))
    (a : PrimeFinAtom ((p - 1) / 10)) :
    a = left.atom ∨ a = right.atom := by
  rcases a.class_cover hp hp10 hnorm with hleft | hright
  · left
    exact (left.atom_eq ⟨a, hleft⟩).symm
  · right
    exact (right.atom_eq ⟨a, hright⟩).symm

theorem PrimeFinAtom.eq_left_of_right_not_contributes
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (c : GeometricSectorCert x)
    (ostar : OrientedSectorNormalization (p := p)
      (PhiInt.star x) c.reflected)
    (left : PrimeClassAtom x ((p - 1) / 10))
    (hright : ¬ Contributes (PhiInt.star x) c.reflected.toSectorCert)
    (a : PrimeFinAtom ((p - 1) / 10)) :
    a = left.atom := by
  rcases a.class_cover hp hp10 hnorm with hleft | hrightClass
  · exact (left.atom_eq ⟨a, hleft⟩).symm
  · exfalso
    apply hright
    apply contributes_of_primeClassAtom hp hp10
      (by rw [PhiInt.norm_star, hnorm]) c.reflected ostar
    exact ⟨a, hrightClass⟩

theorem PrimeFinAtom.eq_right_of_left_not_contributes
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (c : GeometricSectorCert x)
    (o : OrientedSectorNormalization (p := p) x c)
    (right : PrimeClassAtom (PhiInt.star x) ((p - 1) / 10))
    (hleft : ¬ Contributes x c.toSectorCert)
    (a : PrimeFinAtom ((p - 1) / 10)) :
    a = right.atom := by
  rcases a.class_cover hp hp10 hnorm with hleftClass | hright
  · exfalso
    apply hleft
    exact contributes_of_primeClassAtom hp hp10 hnorm c o ⟨a, hleftClass⟩
  · exact (right.atom_eq ⟨a, hright⟩).symm

/-- Exact finite count as the sum of the two geometric contribution
indicators. -/
theorem atomCount_eq_contributes_indicators
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (c : GeometricSectorCert x)
    (o : OrientedSectorNormalization (p := p) x c)
    (ostar : OrientedSectorNormalization (p := p)
      (PhiInt.star x) c.reflected) :
    atomCount ((p - 1) / 10) =
      (if Contributes x c.toSectorCert then 1 else 0) +
      (if Contributes (PhiInt.star x) c.reflected.toSectorCert then 1 else 0) := by
  by_cases hleft : Contributes x c.toSectorCert
  · rcases exists_primeClassAtom_of_contributes hp hp10 hnorm c o hleft with
      ⟨left⟩
    by_cases hright :
        Contributes (PhiInt.star x) c.reflected.toSectorCert
    · rcases exists_primeClassAtom_of_contributes hp hp10
          (by rw [PhiInt.norm_star, hnorm]) c.reflected ostar hright with
        ⟨right⟩
      have hne := left.ne_of_conjugate_classes hp hp10 hnorm right
      have huniv :
          (Finset.univ : Finset (PrimeFinAtom ((p - 1) / 10))) =
            {left.atom, right.atom} := by
        ext a
        simp only [Finset.mem_univ, true_iff, Finset.mem_insert,
          Finset.mem_singleton]
        exact a.eq_left_or_right hp hp10 hnorm left right
      have hcard : atomCount ((p - 1) / 10) = 2 := by
        rw [← PrimeFinAtom.card_eq_atomCount]
        change (Finset.univ :
          Finset (PrimeFinAtom ((p - 1) / 10))).card = 2
        rw [huniv]
        simp [hne]
      simp [hleft, hright, hcard]
    · have huniv :
          (Finset.univ : Finset (PrimeFinAtom ((p - 1) / 10))) =
            {left.atom} := by
        ext a
        simp only [Finset.mem_univ, true_iff, Finset.mem_singleton]
        exact a.eq_left_of_right_not_contributes hp hp10 hnorm c ostar
          left hright
      have hcard : atomCount ((p - 1) / 10) = 1 := by
        rw [← PrimeFinAtom.card_eq_atomCount]
        change (Finset.univ :
          Finset (PrimeFinAtom ((p - 1) / 10))).card = 1
        rw [huniv]
        simp
      simp [hleft, hright, hcard]
  · have hright :
        Contributes (PhiInt.star x) c.reflected.toSectorCert := by
      rcases geometric_at_least_one_contributes hp hp10 hnorm c with h | h
      · exact (hleft h).elim
      · exact h
    rcases exists_primeClassAtom_of_contributes hp hp10
        (by rw [PhiInt.norm_star, hnorm]) c.reflected ostar hright with
      ⟨right⟩
    have huniv :
        (Finset.univ : Finset (PrimeFinAtom ((p - 1) / 10))) =
          {right.atom} := by
      ext a
      simp only [Finset.mem_univ, true_iff, Finset.mem_singleton]
      exact a.eq_right_of_left_not_contributes hp hp10 hnorm c o right hleft
    have hcard : atomCount ((p - 1) / 10) = 1 := by
      rw [← PrimeFinAtom.card_eq_atomCount]
      change (Finset.univ :
        Finset (PrimeFinAtom ((p - 1) / 10))).card = 1
      rw [huniv]
      simp
    simp [hleft, hright, hcard]

theorem atomCount_eq_two_iff_iota_eq_one
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (c : GeometricSectorCert x)
    (o : OrientedSectorNormalization (p := p) x c)
    (ostar : OrientedSectorNormalization (p := p)
      (PhiInt.star x) c.reflected) :
    atomCount ((p - 1) / 10) = 2 ↔
      iotaCert x c.toSectorCert = 1 := by
  rw [atomCount_eq_contributes_indicators hp hp10 hnorm c o ostar]
  have hindicator :
      ((if Contributes x c.toSectorCert then 1 else 0) +
        (if Contributes (PhiInt.star x) c.reflected.toSectorCert then 1 else 0) = 2) ↔
      (Contributes x c.toSectorCert ∧
        Contributes (PhiInt.star x) c.reflected.toSectorCert) := by
    by_cases hleft : Contributes x c.toSectorCert <;>
      by_cases hright :
        Contributes (PhiInt.star x) c.reflected.toSectorCert <;>
      simp [hleft, hright]
  exact hindicator.trans (both_contribute_iff_iota_eq_one hp hp10 hnorm c)

end Ch10
end QseriesFormalization
