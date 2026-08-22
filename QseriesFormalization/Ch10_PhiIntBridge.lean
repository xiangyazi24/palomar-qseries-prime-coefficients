import QseriesFormalization.Ch10_NormTheta_Defs
import Mathlib.Tactic

/-!
# Ch10: Algebraic structure of PhiInt = Z[φ]

Proves PhiInt forms a commutative ring. Establishes norm multiplicativity,
star properties, and that ε is a unit with explicit inverse ε⁻¹ = ⟨2, -1⟩.
-/

namespace QseriesFormalization
namespace Ch10

namespace PhiInt

/-! ### CommRing instance -/

instance : CommRing PhiInt where
  add_assoc x y z := by ext <;> simp <;> ring
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp
  add_comm x y := by ext <;> simp <;> ring
  mul_assoc x y z := by ext <;> simp <;> ring
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp
  left_distrib x y z := by ext <;> simp <;> ring
  right_distrib x y z := by ext <;> simp <;> ring
  mul_comm x y := by ext <;> simp <;> ring
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp
  neg_add_cancel x := by ext <;> simp
  sub_eq_add_neg x y := by ext <;> simp <;> ring
  nsmul := nsmulRec
  zsmul := zsmulRec
  natCast := fun n => ⟨(n : Int), 0⟩
  natCast_zero := rfl
  natCast_succ n := rfl
  intCast := fun n => ⟨n, 0⟩
  intCast_ofNat n := rfl
  intCast_negSucc n := rfl

/-! ### Norm multiplicativity -/

theorem norm_mul (x y : PhiInt) : norm (x * y) = norm x * norm y := by
  simp [norm]; ring

theorem norm_zero : norm 0 = 0 := by simp [norm]

theorem norm_one : norm 1 = 1 := by simp [norm]

theorem norm_neg (x : PhiInt) : norm (-x) = norm x := by
  simp [norm]; try ring

private theorem five_dvd_components_of_norm_eq_zero {a b : Int}
    (h : a ^ 2 + a * b - b ^ 2 = 0) : (5 : Int) ∣ a ∧ (5 : Int) ∣ b := by
  have hp : Nat.Prime 5 := by norm_num
  have hmsq : (2 * a + b) ^ 2 = 5 * b ^ 2 := by nlinarith
  have h5m_sq : (5 : Int) ∣ (2 * a + b) ^ 2 := by
    rw [hmsq]
    exact dvd_mul_right 5 (b ^ 2)
  have h5m : (5 : Int) ∣ 2 * a + b := Int.Prime.dvd_pow' hp h5m_sq
  rcases h5m with ⟨m, hm⟩
  have hleft : (2 * a + b) ^ 2 = 25 * m ^ 2 := by
    rw [hm]
    ring
  have hb_sq : b ^ 2 = 5 * m ^ 2 := by nlinarith
  have h5b_sq : (5 : Int) ∣ b ^ 2 := ⟨m ^ 2, hb_sq⟩
  have h5b : (5 : Int) ∣ b := Int.Prime.dvd_pow' hp h5b_sq
  rcases h5b with ⟨n, hn⟩
  have h5_two_a : (5 : Int) ∣ 2 * a := by
    use m - n
    omega
  have h5a_or : (5 : Int) ∣ (2 : Int) ∨ (5 : Int) ∣ a :=
    Int.Prime.dvd_mul' hp h5_two_a
  constructor
  · rcases h5a_or with h52 | h5a
    · norm_num at h52
    · exact h5a
  · exact ⟨n, hn⟩

private theorem norm_eq_zero_int_aux :
    ∀ n : Nat, ∀ a b : Int, b.natAbs = n →
      a ^ 2 + a * b - b ^ 2 = 0 → a = 0 ∧ b = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro a b hb h
      by_cases hb0 : b = 0
      · have ha_sq : a ^ 2 = 0 := by
          simpa [hb0] using h
        have ha0 : a = 0 := sq_eq_zero_iff.mp ha_sq
        exact ⟨ha0, hb0⟩
      · have h5 := five_dvd_components_of_norm_eq_zero h
        rcases h5.1 with ⟨a', ha'⟩
        rcases h5.2 with ⟨b', hb'⟩
        have hb'_ne : b' ≠ 0 := by
          intro hb'0
          apply hb0
          rw [hb', hb'0, mul_zero]
        have hb_natAbs : b.natAbs = 5 * b'.natAbs := by
          rw [hb', Int.natAbs_mul]
          norm_num
        have hb'_lt : b'.natAbs < n := by
          rw [← hb, hb_natAbs]
          have hb'_pos : 0 < b'.natAbs := Int.natAbs_pos.mpr hb'_ne
          nlinarith
        have hsmall : a' ^ 2 + a' * b' - b' ^ 2 = 0 := by
          have hscale :
              (5 * a') ^ 2 + (5 * a') * (5 * b') - (5 * b') ^ 2 =
                25 * (a' ^ 2 + a' * b' - b' ^ 2) := by
            ring
          have hsubst :
              (5 * a') ^ 2 + (5 * a') * (5 * b') - (5 * b') ^ 2 = 0 := by
            rw [← ha', ← hb']
            exact h
          have hzero : 25 * (a' ^ 2 + a' * b' - b' ^ 2) = 0 := by
            rw [← hscale]
            exact hsubst
          exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)
        have hrec := ih b'.natAbs hb'_lt a' b' rfl hsmall
        constructor <;> omega

theorem norm_eq_zero (x : PhiInt) : norm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hcoords := norm_eq_zero_int_aux x.b.natAbs x.a x.b rfl (by
      simpa [norm] using h)
    ext <;> simp [hcoords.1, hcoords.2]
  · intro h
    rw [h]
    exact norm_zero

theorem eq_zero_of_norm_eq_zero {x : PhiInt} (h : norm x = 0) : x = 0 :=
  (norm_eq_zero x).mp h

instance : Nontrivial PhiInt :=
  ⟨⟨0, 1, by
    intro h
    have ha := congrArg PhiInt.a h
    simp at ha⟩⟩

instance : NoZeroDivisors PhiInt where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro x y hxy
    have hnorm : norm x * norm y = 0 := by
      rw [← norm_mul, hxy, norm_zero]
    rcases mul_eq_zero.mp hnorm with hx | hy
    · exact Or.inl (eq_zero_of_norm_eq_zero hx)
    · exact Or.inr (eq_zero_of_norm_eq_zero hy)

instance : IsDomain PhiInt :=
  NoZeroDivisors.to_isDomain PhiInt

/-! ### Star properties -/

theorem star_star (x : PhiInt) : star (star x) = x := by
  ext <;> simp [star]

theorem star_add (x y : PhiInt) : star (x + y) = star x + star y := by
  ext <;> simp [star] <;> ring

theorem star_mul (x y : PhiInt) : star (x * y) = star x * star y := by
  ext <;> simp [star] <;> ring

theorem star_neg (x : PhiInt) : star (-x) = -(star x) := by
  ext
  · simp [star]
    ring
  · simp [star]

theorem star_zero : star 0 = 0 := by
  ext <;> simp [star]

theorem star_one : star 1 = 1 := by
  ext <;> simp [star]

theorem norm_star (x : PhiInt) : norm (star x) = norm x := by
  simp [norm, star]; ring

/-! ### x * star x = norm x (as integer embedding) -/

theorem mul_star_eq_norm (x : PhiInt) :
    x * star x = ⟨norm x, 0⟩ := by
  ext <;> simp [norm, star] <;> ring

theorem star_mul_eq_norm (x : PhiInt) :
    star x * x = ⟨norm x, 0⟩ := by
  ext <;> simp [norm, star] <;> ring

/-! ### Eps / unit properties -/

theorem norm_eps : norm eps = 1 := by simp [norm, eps]

def epsInv : PhiInt := ⟨2, -1⟩

theorem eps_mul_epsInv : eps * epsInv = 1 := by
  ext <;> simp [eps, epsInv]

theorem epsInv_mul_eps : epsInv * eps = 1 := by
  ext <;> simp [eps, epsInv]

theorem eps_isUnit : IsUnit eps :=
  ⟨⟨eps, epsInv, eps_mul_epsInv, epsInv_mul_eps⟩, rfl⟩

theorem epsInv_isUnit : IsUnit epsInv :=
  ⟨⟨epsInv, eps, epsInv_mul_eps, eps_mul_epsInv⟩, rfl⟩

theorem norm_epsInv : norm epsInv = 1 := by simp [norm, epsInv]

/-! ### Norm and divisibility -/

theorem norm_dvd_of_dvd {x y : PhiInt} (h : x ∣ y) : norm x ∣ norm y := by
  rcases h with ⟨c, hc⟩
  exact ⟨norm c, by rw [hc, norm_mul]⟩

end PhiInt

end Ch10
end QseriesFormalization
