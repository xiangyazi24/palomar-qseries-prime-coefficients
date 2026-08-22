import QseriesFormalization.Ch10_PrimeClassBridge
import Mathlib.Tactic

/-!
# Ch10: Distinctness of the two conjugate prime classes

For norm `-p`, every associate of `x` is determinant-collinear with `x`
modulo `p`.  The conjugate is not: the discriminant identity would otherwise
force `p` to divide both coordinates, contradicting the prime norm.  This
gives a short integral proof that the two classes counted in Paper 3 are
distinct (the ramified exceptional prime `5` is excluded by `p % 10 = 1`).
-/

namespace QseriesFormalization
namespace Ch10

theorem detPhi_mul_same_right (x u : PhiInt) :
    detPhi x (u * x) = u.b * PhiInt.norm x := by
  simp [detPhi, PhiInt.norm]
  ring

@[simp] theorem detPhi_neg_right (x y : PhiInt) :
    detPhi x (-y) = -detPhi x y := by
  simp [detPhi]
  ring

theorem norm_dvd_detPhi_of_sameIdeal {x y : PhiInt}
    (h : sameIdeal x y) :
    PhiInt.norm x ∣ detPhi x y := by
  rcases h with ⟨m, negative, hxy⟩
  rw [hxy]
  cases negative with
  | false =>
      rw [epsZPowMul_eq_zpow_mul, detPhi_mul_same_right]
      exact ⟨((epsUnit ^ m : PhiIntˣ) : PhiInt).b, by ring⟩
  | true =>
      rw [detPhi_neg_right, epsZPowMul_eq_zpow_mul,
        detPhi_mul_same_right]
      exact ⟨-((epsUnit ^ m : PhiIntˣ) : PhiInt).b, by ring⟩

theorem detPhi_self_star (x : PhiInt) :
    detPhi x (PhiInt.star x) = -x.b * Tr x := by
  simp [detPhi, PhiInt.star, Tr]
  ring

theorem prime_not_dvd_b_of_norm_eq_neg_prime
    {p : Nat} (hp : Nat.Prime p) {x : PhiInt}
    (hx : PhiInt.norm x = -(p : Int)) :
    ¬ (p : Int) ∣ x.b := by
  rintro ⟨b₀, hb⟩
  have ha_sq : (p : Int) ∣ x.a ^ 2 := by
    refine ⟨-1 - x.a * b₀ + (p : Int) * b₀ ^ 2, ?_⟩
    rw [PhiInt.norm, hb] at hx
    linear_combination hx
  have ha : (p : Int) ∣ x.a := Int.Prime.dvd_pow' hp ha_sq
  rcases ha with ⟨a₀, ha⟩
  let C : Int := a₀ ^ 2 + a₀ * b₀ - b₀ ^ 2
  have hzero : (p : Int) * ((p : Int) * C + 1) = 0 := by
    dsimp only [C]
    rw [PhiInt.norm, ha, hb] at hx
    linear_combination hx
  have hpzero : (p : Int) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hinner : (p : Int) * C + 1 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hpzero
  have hunit : (p : Int) * C = -1 := by omega
  have hpone_int : (p : Int) ∣ (1 : Int) := by
    refine ⟨-C, ?_⟩
    calc
      (1 : Int) = -((p : Int) * C) := by rw [hunit]; norm_num
      _ = (p : Int) * (-C) := by ring
  have hpone : p ∣ 1 := by exact_mod_cast hpone_int
  have hle : p ≤ 1 := Nat.le_of_dvd (by decide) hpone
  have hp_two := hp.two_le
  omega

theorem prime_not_dvd_detPhi_star
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hx : PhiInt.norm x = -(p : Int)) :
    ¬ (p : Int) ∣ detPhi x (PhiInt.star x) := by
  intro hdet
  have hprod : (p : Int) ∣ x.b * Tr x := by
    rw [detPhi_self_star] at hdet
    have hneg : (p : Int) ∣ -(x.b * Tr x) := by
      simpa [neg_mul] using hdet
    exact dvd_neg.mp hneg
  rcases Int.Prime.dvd_mul' hp hprod with hb | htrace
  · exact prime_not_dvd_b_of_norm_eq_neg_prime hp hx hb
  · rcases htrace with ⟨q, hq⟩
    have hdisc := trace_sq_sub_five_b_sq x
    rw [hx, hq] at hdisc
    have h5b_sq : (p : Int) ∣ 5 * x.b ^ 2 := by
      refine ⟨(p : Int) * q ^ 2 + 4, ?_⟩
      nlinarith
    rcases Int.Prime.dvd_mul' hp h5b_sq with hfive | hb_sq
    · have hfive_nat : p ∣ 5 := by exact_mod_cast hfive
      have hle : p ≤ 5 := Nat.le_of_dvd (by norm_num) hfive_nat
      have hp_two := hp.two_le
      omega
    · have hb : (p : Int) ∣ x.b := Int.Prime.dvd_pow' hp hb_sq
      exact prime_not_dvd_b_of_norm_eq_neg_prime hp hx hb

/-- The two conjugate norm-prime elements represent distinct unit orbits. -/
theorem not_sameIdeal_star_of_norm_eq_neg_prime
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hx : PhiInt.norm x = -(p : Int)) :
    ¬ sameIdeal x (PhiInt.star x) := by
  intro hassoc
  have hnorm_dvd := norm_dvd_detPhi_of_sameIdeal hassoc
  have hpdet : (p : Int) ∣ detPhi x (PhiInt.star x) := by
    rw [hx] at hnorm_dvd
    simpa using hnorm_dvd
  exact prime_not_dvd_detPhi_star hp hp10 hx hpdet

theorem PrimeClassAtom.ne_of_conjugate_classes
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hx : PhiInt.norm x = -(p : Int))
    (left : PrimeClassAtom x ((p - 1) / 10))
    (right : PrimeClassAtom (PhiInt.star x) ((p - 1) / 10)) :
    left.atom ≠ right.atom := by
  intro heq
  apply not_sameIdeal_star_of_norm_eq_neg_prime hp hp10 hx
  apply sameIdeal_trans left.same
  apply sameIdeal_symm
  simpa [heq] using right.same

end Ch10
end QseriesFormalization
