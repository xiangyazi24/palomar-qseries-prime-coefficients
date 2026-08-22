import QseriesFormalization.Ch10_SplitPrimeExistence
import QseriesFormalization.Ch10_OneAtom
import Mathlib.Tactic

/-!
# Ch10: The two norm-prime orbits

For a split prime, the norm form factors into two distinct lines modulo the
prime.  Elements of norm `-p` on the same line differ by an integral element
of norm one; elements on opposite lines differ after conjugation.  This gives
the algebraic two-orbit statement without invoking ideal class groups, PID
instances, or a classification of all units.
-/

namespace QseriesFormalization
namespace Ch10

@[simp] theorem PhiInt.intCast_a (n : Int) : ((n : PhiInt).a) = n := rfl
@[simp] theorem PhiInt.intCast_b (n : Int) : ((n : PhiInt).b) = 0 := rfl

theorem PhiInt.mul_intCast (x : PhiInt) (n : Int) :
    x * (n : PhiInt) = ⟨x.a * n, x.b * n⟩ := by
  ext <;> simp only [PhiInt.mul_a, PhiInt.mul_b, PhiInt.intCast_a,
    PhiInt.intCast_b] <;> ring

theorem PhiInt.intCast_mul (n : Int) (x : PhiInt) :
    (n : PhiInt) * x = ⟨n * x.a, n * x.b⟩ := by
  ext <;> simp only [PhiInt.mul_a, PhiInt.mul_b, PhiInt.intCast_a,
    PhiInt.intCast_b] <;> ring

def normLineMinus (p : Nat) (t : ZMod p) (x : PhiInt) : ZMod p :=
  2 * (x.a : ZMod p) + (1 - t) * (x.b : ZMod p)

def normLinePlus (p : Nat) (t : ZMod p) (x : PhiInt) : ZMod p :=
  2 * (x.a : ZMod p) + (1 + t) * (x.b : ZMod p)

theorem normLine_factorization (p : Nat) (t : ZMod p)
    (ht : (5 : ZMod p) = t ^ 2) (x : PhiInt) :
    normLineMinus p t x * normLinePlus p t x =
      4 * ((PhiInt.norm x : Int) : ZMod p) := by
  calc
    normLineMinus p t x * normLinePlus p t x =
        4 * ((PhiInt.norm x : Int) : ZMod p) +
          (5 - t ^ 2) * (x.b : ZMod p) ^ 2 := by
            unfold normLineMinus normLinePlus PhiInt.norm
            push_cast
            ring
    _ = 4 * ((PhiInt.norm x : Int) : ZMod p) := by rw [ht]; ring

/-- An element of norm `-p` lies on one of the two norm-zero lines modulo p. -/
theorem normLine_cases_of_norm_eq_neg_prime
    {p : Nat} (hp : Nat.Prime p) {t : ZMod p}
    (ht : (5 : ZMod p) = t ^ 2) {x : PhiInt}
    (hnorm : PhiInt.norm x = -(p : Int)) :
    normLineMinus p t x = 0 ∨ normLinePlus p t x = 0 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hfactor := normLine_factorization p t ht x
  have hcast : ((PhiInt.norm x : Int) : ZMod p) = 0 := by
    rw [hnorm]
    simp
  rw [hcast, mul_zero] at hfactor
  exact mul_eq_zero.mp hfactor

theorem normLineMinus_star (p : Nat) (t : ZMod p) (x : PhiInt) :
    normLineMinus p t (PhiInt.star x) = normLinePlus p t x := by
  simp [normLineMinus, normLinePlus, PhiInt.star]
  ring

theorem normLinePlus_star (p : Nat) (t : ZMod p) (x : PhiInt) :
    normLinePlus p t (PhiInt.star x) = normLineMinus p t x := by
  simp [normLineMinus, normLinePlus, PhiInt.star]
  ring

private theorem two_ne_zero_zmod_of_prime_mod10_one
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1) :
    (2 : ZMod p) ≠ 0 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  intro hzero
  have hdiv : p ∣ 2 :=
    (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hzero)
  have hp_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
  have hp_two_le := hp.two_le
  omega

private theorem four_ne_zero_zmod_of_prime_mod10_one
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1) :
    (4 : ZMod p) ≠ 0 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  intro hzero
  have hdiv : p ∣ 4 :=
    (ZMod.natCast_eq_zero_iff 4 p).mp (by simpa using hzero)
  have hp_le : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdiv
  have hp_two_le := hp.two_le
  omega

/-- On either fixed norm line, `y * star x` vanishes coefficientwise modulo p. -/
theorem mul_star_mod_eq_zero_of_same_normLine
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {t : ZMod p} (ht : (5 : ZMod p) = t ^ 2) {x y : PhiInt}
    (hline :
      (normLineMinus p t x = 0 ∧ normLineMinus p t y = 0) ∨
      (normLinePlus p t x = 0 ∧ normLinePlus p t y = 0)) :
    (((y * PhiInt.star x).a : Int) : ZMod p) = 0 ∧
      (((y * PhiInt.star x).b : Int) : ZMod p) = 0 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have htwo := two_ne_zero_zmod_of_prime_mod10_one hp hp10
  have hfour := four_ne_zero_zmod_of_prime_mod10_one hp hp10
  have htzero : t ^ 2 - 5 = 0 := sub_eq_zero.mpr ht.symm
  rcases hline with hminus | hplus
  · simp only [normLineMinus] at hminus
    have hx :
        2 * (x.a : ZMod p) = -(1 - t) * (x.b : ZMod p) := by
      linear_combination hminus.1
    have hy :
        2 * (y.a : ZMod p) = -(1 - t) * (y.b : ZMod p) := by
      linear_combination hminus.2
    constructor
    · have h4a :
          (4 : ZMod p) * (((y * PhiInt.star x).a : Int) : ZMod p) = 0 := by
        simp only [PhiInt.mul_a, PhiInt.star]
        push_cast
        calc
          (4 : ZMod p) *
              ((y.a : ZMod p) * ((x.a : ZMod p) + (x.b : ZMod p)) +
                (y.b : ZMod p) * (-(x.b : ZMod p))) =
              (2 * (y.a : ZMod p)) * (2 * (x.a : ZMod p)) +
                2 * (2 * (y.a : ZMod p)) * (x.b : ZMod p) -
                4 * (y.b : ZMod p) * (x.b : ZMod p) := by ring
          _ = (t ^ 2 - 5) * (y.b : ZMod p) * (x.b : ZMod p) := by
            rw [hx, hy]
            ring
          _ = 0 := by rw [htzero]; simp
      exact (mul_eq_zero.mp h4a).resolve_left hfour
    · have h2b :
          (2 : ZMod p) * (((y * PhiInt.star x).b : Int) : ZMod p) = 0 := by
        simp only [PhiInt.mul_b, PhiInt.star]
        push_cast
        calc
          (2 : ZMod p) *
              ((y.a : ZMod p) * (-(x.b : ZMod p)) +
                (y.b : ZMod p) * ((x.a : ZMod p) + (x.b : ZMod p)) +
                (y.b : ZMod p) * (-(x.b : ZMod p))) =
              -(2 * (y.a : ZMod p)) * (x.b : ZMod p) +
                (y.b : ZMod p) * (2 * (x.a : ZMod p)) := by ring
          _ = 0 := by rw [hx, hy]; ring
      exact (mul_eq_zero.mp h2b).resolve_left htwo
  · simp only [normLinePlus] at hplus
    have hx :
        2 * (x.a : ZMod p) = -(1 + t) * (x.b : ZMod p) := by
      linear_combination hplus.1
    have hy :
        2 * (y.a : ZMod p) = -(1 + t) * (y.b : ZMod p) := by
      linear_combination hplus.2
    constructor
    · have h4a :
          (4 : ZMod p) * (((y * PhiInt.star x).a : Int) : ZMod p) = 0 := by
        simp only [PhiInt.mul_a, PhiInt.star]
        push_cast
        calc
          (4 : ZMod p) *
              ((y.a : ZMod p) * ((x.a : ZMod p) + (x.b : ZMod p)) +
                (y.b : ZMod p) * (-(x.b : ZMod p))) =
              (2 * (y.a : ZMod p)) * (2 * (x.a : ZMod p)) +
                2 * (2 * (y.a : ZMod p)) * (x.b : ZMod p) -
                4 * (y.b : ZMod p) * (x.b : ZMod p) := by ring
          _ = (t ^ 2 - 5) * (y.b : ZMod p) * (x.b : ZMod p) := by
            rw [hx, hy]
            ring
          _ = 0 := by rw [htzero]; simp
      exact (mul_eq_zero.mp h4a).resolve_left hfour
    · have h2b :
          (2 : ZMod p) * (((y * PhiInt.star x).b : Int) : ZMod p) = 0 := by
        simp only [PhiInt.mul_b, PhiInt.star]
        push_cast
        calc
          (2 : ZMod p) *
              ((y.a : ZMod p) * (-(x.b : ZMod p)) +
                (y.b : ZMod p) * ((x.a : ZMod p) + (x.b : ZMod p)) +
                (y.b : ZMod p) * (-(x.b : ZMod p))) =
              -(2 * (y.a : ZMod p)) * (x.b : ZMod p) +
                (y.b : ZMod p) * (2 * (x.a : ZMod p)) := by ring
          _ = 0 := by rw [hx, hy]; ring
      exact (mul_eq_zero.mp h2b).resolve_left htwo

/-- Coefficientwise divisibility of `y * star x` yields an integral norm-one
quotient taking `x` to `y`. -/
theorem exists_norm_one_quotient_of_mul_star_mod_eq_zero
    {p : Nat} (hp : Nat.Prime p) {x y : PhiInt}
    (hxnorm : PhiInt.norm x = -(p : Int))
    (hynorm : PhiInt.norm y = -(p : Int))
    (hmod : (((y * PhiInt.star x).a : Int) : ZMod p) = 0 ∧
      (((y * PhiInt.star x).b : Int) : ZMod p) = 0) :
    ∃ u : PhiInt, PhiInt.norm u = 1 ∧ y = u * x := by
  have hp_pos : 0 < (p : Int) := by exact_mod_cast hp.pos
  have hpa : (p : Int) ∣ (y * PhiInt.star x).a :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (y * PhiInt.star x).a p).mp hmod.1
  have hpb : (p : Int) ∣ (y * PhiInt.star x).b :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (y * PhiInt.star x).b p).mp hmod.2
  rcases hpa with ⟨ua, hua⟩
  rcases hpb with ⟨ub, hub⟩
  let q : PhiInt := ⟨ua, ub⟩
  let u : PhiInt := -q
  have hw : y * PhiInt.star x = ((p : Int) : PhiInt) * q := by
    rw [PhiInt.intCast_mul]
    ext
    · simpa [q] using hua
    · simpa [q] using hub
  have hp_cast_ne : (((p : Int) : PhiInt)) ≠ 0 := by
    intro hzero
    have := congrArg PhiInt.a hzero
    change (p : Int) = 0 at this
    have hp_ne : (p : Int) ≠ 0 := by exact_mod_cast hp.ne_zero
    exact hp_ne this
  have hyux : y = u * x := by
    apply (mul_left_cancel₀ hp_cast_ne)
    rw [mul_comm ((p : Int) : PhiInt) y]
    calc
      y * ((p : Int) : PhiInt) =
          -(y * (PhiInt.star x * x)) := by
            rw [PhiInt.star_mul_eq_norm, hxnorm]
            ext <;> simp only [PhiInt.mul_a, PhiInt.mul_b,
              PhiInt.intCast_a, PhiInt.intCast_b, PhiInt.neg_a,
              PhiInt.neg_b] <;> ring
      _ = -((y * PhiInt.star x) * x) := by ring
      _ = -((((p : Int) : PhiInt) * q) * x) := by rw [hw]
      _ = ((p : Int) : PhiInt) * (u * x) := by simp [u]; ring
  have hunorm : PhiInt.norm u = 1 := by
    have hnorm_mul := PhiInt.norm_mul u x
    rw [← hyux, hynorm, hxnorm] at hnorm_mul
    nlinarith
  exact ⟨u, hunorm, hyux⟩

/-- Same norm line means the two norm-prime elements differ by an integral
norm-one multiplier. -/
theorem exists_norm_one_quotient_of_same_normLine
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {t : ZMod p} (ht : (5 : ZMod p) = t ^ 2) {x y : PhiInt}
    (hxnorm : PhiInt.norm x = -(p : Int))
    (hynorm : PhiInt.norm y = -(p : Int))
    (hline :
      (normLineMinus p t x = 0 ∧ normLineMinus p t y = 0) ∨
      (normLinePlus p t x = 0 ∧ normLinePlus p t y = 0)) :
    ∃ u : PhiInt, PhiInt.norm u = 1 ∧ y = u * x := by
  apply exists_norm_one_quotient_of_mul_star_mod_eq_zero hp hxnorm hynorm
  exact mul_star_mod_eq_zero_of_same_normLine hp hp10 ht hline

/-- Every two elements of norm `-p` differ either within one norm-one orbit or
after conjugating one of them. -/
theorem norm_prime_two_orbits
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {t : ZMod p} (ht : (5 : ZMod p) = t ^ 2) {x y : PhiInt}
    (hxnorm : PhiInt.norm x = -(p : Int))
    (hynorm : PhiInt.norm y = -(p : Int)) :
    (∃ u : PhiInt, PhiInt.norm u = 1 ∧ y = u * x) ∨
      (∃ u : PhiInt, PhiInt.norm u = 1 ∧ y = u * PhiInt.star x) := by
  have hxlines := normLine_cases_of_norm_eq_neg_prime hp ht hxnorm
  have hylines := normLine_cases_of_norm_eq_neg_prime hp ht hynorm
  rcases hxlines with hxm | hxp <;> rcases hylines with hym | hyp
  · left
    exact exists_norm_one_quotient_of_same_normLine hp hp10 ht hxnorm hynorm
      (Or.inl ⟨hxm, hym⟩)
  · right
    have hstar_norm : PhiInt.norm (PhiInt.star x) = -(p : Int) := by
      rw [PhiInt.norm_star, hxnorm]
    exact exists_norm_one_quotient_of_same_normLine hp hp10 ht hstar_norm hynorm
      (Or.inr ⟨by simpa [normLinePlus_star] using hxm, hyp⟩)
  · right
    have hstar_norm : PhiInt.norm (PhiInt.star x) = -(p : Int) := by
      rw [PhiInt.norm_star, hxnorm]
    exact exists_norm_one_quotient_of_same_normLine hp hp10 ht hstar_norm hynorm
      (Or.inl ⟨by simpa [normLineMinus_star] using hxp, hym⟩)
  · left
    exact exists_norm_one_quotient_of_same_normLine hp hp10 ht hxnorm hynorm
      (Or.inr ⟨hxp, hyp⟩)

end Ch10
end QseriesFormalization
