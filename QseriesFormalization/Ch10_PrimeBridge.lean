import QseriesFormalization.Ch10_SignCoherence
import QseriesFormalization.Ch10_NormTheta_Coeff
import QseriesFormalization.Ch10_SplitPrime

/-!
# Ch10: Finite bridge from prime atoms to `BCoeff`

The finite sets below are exactly the filtered sets occurring in `ACoeff` and
`DCoeff`.  A prime atom certificate records the finite consequences of ideal
assignment, one-atom uniqueness, and sign coherence.  It does not contain a
coefficient equality: that equality is derived here from the definition of
`BCoeff`.
-/

namespace QseriesFormalization
namespace Ch10

def AAtoms (N : Nat) : Finset (Nat × Nat) :=
  ((Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
    (fun q => E (↑q.1) (↑q.2) = ↑N))

def DAtoms (N : Nat) : Finset (Nat × Nat) :=
  ((Finset.range (N + 1) ×ˢ Finset.range (2 * N + 2)).filter
    (fun q => E (-((↑q.1 : Int) + 1)) (-((↑q.2 : Int) + 1)) = ↑N))

def AAtomWeight (q : Nat × Nat) : Int :=
  -negOnePowInt (↑q.2)

def DAtomWeight (q : Nat × Nat) : Int :=
  negOnePowInt (-((↑q.2 : Int) + 1))

def atomCount (N : Nat) : Nat := (AAtoms N).card + (DAtoms N).card

theorem BCoeff_eq_atom_sums (N : Nat) :
    BCoeff N =
      (AAtoms N).sum AAtomWeight + (DAtoms N).sum DAtomWeight := by
  unfold BCoeff ACoeff DCoeff AAtoms DAtoms AAtomWeight DAtomWeight
  ring

private theorem finset_sum_eq_sign_mul_card
    {X : Type} [DecidableEq X] (S : Finset X) (w : X → Int) (s : Int)
    (h : ∀ x ∈ S, w x = s) :
    S.sum w = s * (S.card : Int) := by
  calc
    S.sum w = S.sum (fun _ => s) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact h x hx
    _ = s * (S.card : Int) := by simp [mul_comm]

/-- If all atoms at a level have sign `s`, `BCoeff` is `s` times their count. -/
theorem BCoeff_eq_signed_atom_count (N : Nat) (s : Int)
    (hA : ∀ q ∈ AAtoms N, AAtomWeight q = s)
    (hD : ∀ q ∈ DAtoms N, DAtomWeight q = s) :
    BCoeff N = s * (atomCount N : Int) := by
  rw [BCoeff_eq_atom_sums,
    finset_sum_eq_sign_mul_card (AAtoms N) AAtomWeight s hA,
    finset_sum_eq_sign_mul_card (DAtoms N) DAtomWeight s hD]
  simp only [atomCount, Nat.cast_add]
  ring

theorem negOnePowInt_eq_one_or_neg_one (n : Int) :
    negOnePowInt n = 1 ∨ negOnePowInt n = -1 := by
  unfold negOnePowInt
  by_cases h : n % 2 = 0 <;> simp [h]

theorem AAtomWeight_eq_one_or_neg_one (q : Nat × Nat) :
    AAtomWeight q = 1 ∨ AAtomWeight q = -1 := by
  rcases negOnePowInt_eq_one_or_neg_one (↑q.2) with h | h
  · right; simp [AAtomWeight, h]
  · left; simp [AAtomWeight, h]

theorem DAtomWeight_eq_one_or_neg_one (q : Nat × Nat) :
    DAtomWeight q = 1 ∨ DAtomWeight q = -1 := by
  simpa [DAtomWeight] using
    negOnePowInt_eq_one_or_neg_one (-((↑q.2 : Int) + 1))

/--
Finite certificate for the missing ideal-to-coefficient bridge.

`one_atom_bound` is the finite form of one-atom uniqueness (at most one atom
for each of the two conjugate ideals).  `all_A` and `all_D` are the finite form
of sign coherence.  The last two fields turn either good iota class into an
actual atom in the defining finite sets.
-/
structure PrimeAtomCertificate {p : Nat} (sp : SplitPrimeCert p)
    (c : SectorCert sp.π) where
  sign : Int
  all_A : ∀ q ∈ AAtoms ((p - 1) / 10), AAtomWeight q = sign
  all_D : ∀ q ∈ DAtoms ((p - 1) / 10), DAtomWeight q = sign
  one_atom_bound : atomCount ((p - 1) / 10) ≤ 2
  atom_of_left_contributes :
    Contributes sp.π c → 0 < atomCount ((p - 1) / 10)
  atom_of_right_contributes :
    Contributes (PhiInt.star sp.π) (reflectedSectorCert sp.π c) →
      0 < atomCount ((p - 1) / 10)

/-- Prime coefficient nonvanishing and magnitude classification. -/
theorem prime_coeff_classification {p : Nat} (sp : SplitPrimeCert p)
    (c : SectorCert sp.π) (atoms : PrimeAtomCertificate sp c) :
    BCoeff ((p - 1) / 10) ∈ ({-2, -1, 1, 2} : Set Int) := by
  have hcontrib := splitPrimeCert_at_least_one_contributes sp c
  have hpos : 0 < atomCount ((p - 1) / 10) := by
    rcases hcontrib with hleft | hright
    · exact atoms.atom_of_left_contributes hleft
    · exact atoms.atom_of_right_contributes hright
  have hcoeff := BCoeff_eq_signed_atom_count ((p - 1) / 10) atoms.sign
    atoms.all_A atoms.all_D
  have hle := atoms.one_atom_bound
  have hnonempty :
      (AAtoms ((p - 1) / 10)).Nonempty ∨
        (DAtoms ((p - 1) / 10)).Nonempty := by
    by_cases hA : (AAtoms ((p - 1) / 10)).Nonempty
    · exact Or.inl hA
    · right
      by_contra hD
      have hA0 : AAtoms ((p - 1) / 10) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hA
      have hD0 : DAtoms ((p - 1) / 10) = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hD
      simpa [atomCount, hA0, hD0] using hpos
  have hsign : atoms.sign = 1 ∨ atoms.sign = -1 := by
    rcases hnonempty with ⟨q, hq⟩ | ⟨q, hq⟩
    · have hqsign := atoms.all_A q hq
      rcases AAtomWeight_eq_one_or_neg_one q with h | h
      · left; omega
      · right; omega
    · have hqsign := atoms.all_D q hq
      rcases DAtomWeight_eq_one_or_neg_one q with h | h
      · left; omega
      · right; omega
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases hsign with hs | hs
  · rw [hs] at hcoeff
    omega
  · rw [hs] at hcoeff
    omega

theorem prime_coeff_ne_zero {p : Nat} (sp : SplitPrimeCert p)
    (c : SectorCert sp.π) (atoms : PrimeAtomCertificate sp c) :
    BCoeff ((p - 1) / 10) ≠ 0 := by
  have hclass := prime_coeff_classification sp c atoms
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hclass
  rcases hclass with h | h | h | h <;> omega

end Ch10
end QseriesFormalization
