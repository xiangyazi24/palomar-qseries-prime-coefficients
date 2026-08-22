import QseriesFormalization.Ch10_PrimeOrbit
import Mathlib.Tactic

/-!
# Ch10: Norm-one units of `Z[phi]`

An elementary descent on the second coordinate proves that every norm-one
element is a signed integral power of `eps`.  This is the exact unit theorem
needed to turn the norm-one quotients in `Ch10_PrimeOrbit` into the existing
`sameIdeal` relation.
-/

namespace QseriesFormalization
namespace Ch10

def epsUnit : PhiIntˣ where
  val := PhiInt.eps
  inv := PhiInt.epsInv
  val_inv := PhiInt.eps_mul_epsInv
  inv_val := PhiInt.epsInv_mul_eps

@[simp] theorem epsUnit_val : (epsUnit : PhiInt) = PhiInt.eps := rfl
@[simp] theorem epsUnit_inv_val : ((epsUnit⁻¹ : PhiIntˣ) : PhiInt) = PhiInt.epsInv := rfl

theorem epsMul_eq_mul (x : PhiInt) : epsMul x = PhiInt.eps * x := by
  ext
  · simp [epsMul, PhiInt.eps]
  · simp [epsMul, PhiInt.eps]
    ring

theorem epsInvMul_eq_mul (x : PhiInt) : epsInvMul x = PhiInt.epsInv * x := by
  ext <;> simp [epsInvMul, PhiInt.epsInv] <;> ring

theorem epsMul_epsInvMul (x : PhiInt) : epsMul (epsInvMul x) = x := by
  rw [epsMul_eq_mul, epsInvMul_eq_mul]
  calc
    PhiInt.eps * (PhiInt.epsInv * x) =
        (PhiInt.eps * PhiInt.epsInv) * x := by ring
    _ = x := by rw [PhiInt.eps_mul_epsInv, one_mul]

theorem epsInvMul_epsMul (x : PhiInt) : epsInvMul (epsMul x) = x := by
  rw [epsMul_eq_mul, epsInvMul_eq_mul]
  calc
    PhiInt.epsInv * (PhiInt.eps * x) =
        (PhiInt.epsInv * PhiInt.eps) * x := by ring
    _ = x := by rw [PhiInt.epsInv_mul_eps, one_mul]

theorem norm_epsMul (x : PhiInt) : PhiInt.norm (epsMul x) = PhiInt.norm x := by
  rw [epsMul_eq_mul, PhiInt.norm_mul, PhiInt.norm_eps, one_mul]

theorem norm_epsInvMul (x : PhiInt) :
    PhiInt.norm (epsInvMul x) = PhiInt.norm x := by
  rw [epsInvMul_eq_mul, PhiInt.norm_mul, PhiInt.norm_epsInv, one_mul]

@[simp] theorem norm_epsNatMul (n : Nat) (x : PhiInt) :
    PhiInt.norm (epsNatMul n x) = PhiInt.norm x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [epsNatMul, norm_epsMul, ih]

@[simp] theorem norm_epsInvNatMul (n : Nat) (x : PhiInt) :
    PhiInt.norm (epsInvNatMul n x) = PhiInt.norm x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [epsInvNatMul, norm_epsInvMul, ih]

@[simp] theorem norm_epsZPowMul (m : Int) (x : PhiInt) :
    PhiInt.norm (epsZPowMul m x) = PhiInt.norm x := by
  cases m <;> simp [epsZPowMul]

theorem trace_sq_sub_five_b_sq (x : PhiInt) :
    Tr x ^ 2 - 5 * x.b ^ 2 = 4 * PhiInt.norm x := by
  simp [Tr, PhiInt.norm]
  ring

theorem epsUnit_mul_zpow_val (m : Int) :
    PhiInt.eps * ((epsUnit ^ m : PhiIntˣ) : PhiInt) =
      ((epsUnit ^ (m + 1) : PhiIntˣ) : PhiInt) := by
  have h : epsUnit * epsUnit ^ m = epsUnit ^ (m + 1) := by
    simpa [mul_comm] using (zpow_add_one epsUnit m).symm
  exact congrArg (fun u : PhiIntˣ => (u : PhiInt)) h

theorem epsUnit_inv_mul_zpow_val (m : Int) :
    PhiInt.epsInv * ((epsUnit ^ m : PhiIntˣ) : PhiInt) =
      ((epsUnit ^ (m - 1) : PhiIntˣ) : PhiInt) := by
  have h : epsUnit⁻¹ * epsUnit ^ m = epsUnit ^ (m - 1) := by
    simpa [mul_comm] using (zpow_sub_one epsUnit m).symm
  exact congrArg (fun u : PhiIntˣ => (u : PhiInt)) h

private theorem norm_one_signed_epsUnit_zpow_of_b_nonneg :
    ∀ n : Nat, ∀ u : PhiInt, u.b.natAbs = n → 0 ≤ u.b →
      PhiInt.norm u = 1 →
      ∃ m : Int,
        u = ((epsUnit ^ m : PhiIntˣ) : PhiInt) ∨
          u = -((epsUnit ^ m : PhiIntˣ) : PhiInt) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro u hbabs hb_nonneg hunorm
      by_cases hbzero : u.b = 0
      · have ha_sq : u.a ^ 2 = 1 := by
          simpa [PhiInt.norm, hbzero] using hunorm
        by_cases ha_nonneg : 0 ≤ u.a
        · have ha : u.a = 1 := by nlinarith
          refine ⟨0, Or.inl ?_⟩
          ext
          · simp [ha]
          · simp [hbzero]
        · have ha : u.a = -1 := by
            have ha_neg : u.a < 0 := lt_of_not_ge ha_nonneg
            nlinarith
          refine ⟨0, Or.inr ?_⟩
          ext
          · simp [ha]
          · simp [hbzero]
      · have hb_pos : 0 < u.b := lt_of_le_of_ne hb_nonneg (Ne.symm hbzero)
        have hpell := trace_sq_sub_five_b_sq u
        rw [hunorm] at hpell
        have htrace_ne : Tr u ≠ 0 := by
          intro hzero
          rw [hzero] at hpell
          nlinarith [sq_pos_of_pos hb_pos]
        rcases lt_or_gt_of_ne htrace_ne with htrace_neg | htrace_pos
        · have htwo : 2 * u.b < -(Tr u) := by
            by_contra h
            have hle : -(Tr u) ≤ 2 * u.b := by omega
            have hprod :
                0 ≤ (2 * u.b - (-(Tr u))) * (2 * u.b + (-(Tr u))) :=
              mul_nonneg (by omega) (by omega)
            nlinarith [sq_pos_of_pos hb_pos]
          have hthree : -(Tr u) ≤ 3 * u.b := by
            by_contra h
            have hgt : 3 * u.b < -(Tr u) := by omega
            have hprod :
                0 < ((-(Tr u)) - 3 * u.b) * ((-(Tr u)) + 3 * u.b) :=
              mul_pos (by omega) (by omega)
            have hb_sq_ge : 1 ≤ u.b ^ 2 := by nlinarith
            nlinarith
          let v := epsMul u
          have hvb_nonneg : 0 ≤ v.b := by
            simp only [v, epsMul]
            simp only [Tr] at htrace_neg htwo hthree
            omega
          have hvb_lt : v.b < u.b := by
            simp only [v, epsMul]
            simp only [Tr] at htrace_neg htwo hthree
            omega
          have hvabs_lt : v.b.natAbs < n := by
            rw [← hbabs]
            have hv_cast : (v.b.natAbs : Int) = v.b := by
              rw [Int.natCast_natAbs, abs_of_nonneg hvb_nonneg]
            have hu_cast : (u.b.natAbs : Int) = u.b := by
              rw [Int.natCast_natAbs, abs_of_nonneg hb_nonneg]
            exact_mod_cast (show (v.b.natAbs : Int) < (u.b.natAbs : Int) by omega)
          have hvnorm : PhiInt.norm v = 1 := by
            simpa [v] using (norm_epsMul u).trans hunorm
          rcases ih v.b.natAbs hvabs_lt v rfl hvb_nonneg hvnorm with
            ⟨m, hm | hm⟩
          · refine ⟨m - 1, Or.inl ?_⟩
            calc
              u = epsInvMul v := by simp [v, epsInvMul_epsMul]
              _ = PhiInt.epsInv * v := epsInvMul_eq_mul v
              _ = PhiInt.epsInv * ((epsUnit ^ m : PhiIntˣ) : PhiInt) := by rw [hm]
              _ = ((epsUnit ^ (m - 1) : PhiIntˣ) : PhiInt) :=
                epsUnit_inv_mul_zpow_val m
          · refine ⟨m - 1, Or.inr ?_⟩
            calc
              u = epsInvMul v := by simp [v, epsInvMul_epsMul]
              _ = PhiInt.epsInv * v := epsInvMul_eq_mul v
              _ = PhiInt.epsInv *
                    (-((epsUnit ^ m : PhiIntˣ) : PhiInt)) := by rw [hm]
              _ = -((epsUnit ^ (m - 1) : PhiIntˣ) : PhiInt) := by
                rw [mul_neg, epsUnit_inv_mul_zpow_val]
        · have htwo : 2 * u.b < Tr u := by
            by_contra h
            have hle : Tr u ≤ 2 * u.b := by omega
            have hprod :
                0 ≤ (2 * u.b - Tr u) * (2 * u.b + Tr u) :=
              mul_nonneg (by omega) (by omega)
            nlinarith [sq_pos_of_pos hb_pos]
          have hthree : Tr u ≤ 3 * u.b := by
            by_contra h
            have hgt : 3 * u.b < Tr u := by omega
            have hprod :
                0 < (Tr u - 3 * u.b) * (Tr u + 3 * u.b) :=
              mul_pos (by omega) (by omega)
            have hb_sq_ge : 1 ≤ u.b ^ 2 := by nlinarith
            nlinarith
          let v := epsInvMul u
          have hvb_nonneg : 0 ≤ v.b := by
            simp only [v, epsInvMul]
            simp only [Tr] at htrace_pos htwo hthree
            omega
          have hvb_lt : v.b < u.b := by
            simp only [v, epsInvMul]
            simp only [Tr] at htrace_pos htwo hthree
            omega
          have hvabs_lt : v.b.natAbs < n := by
            rw [← hbabs]
            have hv_cast : (v.b.natAbs : Int) = v.b := by
              rw [Int.natCast_natAbs, abs_of_nonneg hvb_nonneg]
            have hu_cast : (u.b.natAbs : Int) = u.b := by
              rw [Int.natCast_natAbs, abs_of_nonneg hb_nonneg]
            exact_mod_cast (show (v.b.natAbs : Int) < (u.b.natAbs : Int) by omega)
          have hvnorm : PhiInt.norm v = 1 := by
            simpa [v] using (norm_epsInvMul u).trans hunorm
          rcases ih v.b.natAbs hvabs_lt v rfl hvb_nonneg hvnorm with
            ⟨m, hm | hm⟩
          · refine ⟨m + 1, Or.inl ?_⟩
            calc
              u = epsMul v := by simp [v, epsMul_epsInvMul]
              _ = PhiInt.eps * v := epsMul_eq_mul v
              _ = PhiInt.eps * ((epsUnit ^ m : PhiIntˣ) : PhiInt) := by rw [hm]
              _ = ((epsUnit ^ (m + 1) : PhiIntˣ) : PhiInt) :=
                epsUnit_mul_zpow_val m
          · refine ⟨m + 1, Or.inr ?_⟩
            calc
              u = epsMul v := by simp [v, epsMul_epsInvMul]
              _ = PhiInt.eps * v := epsMul_eq_mul v
              _ = PhiInt.eps *
                    (-((epsUnit ^ m : PhiIntˣ) : PhiInt)) := by rw [hm]
              _ = -((epsUnit ^ (m + 1) : PhiIntˣ) : PhiInt) := by
                rw [mul_neg, epsUnit_mul_zpow_val]

/-- Every norm-one element is a signed integral power of `eps`. -/
theorem norm_one_eq_sign_epsUnit_zpow (u : PhiInt)
    (hu : PhiInt.norm u = 1) :
    ∃ m : Int,
      u = ((epsUnit ^ m : PhiIntˣ) : PhiInt) ∨
        u = -((epsUnit ^ m : PhiIntˣ) : PhiInt) := by
  by_cases hb : 0 ≤ u.b
  · exact norm_one_signed_epsUnit_zpow_of_b_nonneg u.b.natAbs u rfl hb hu
  · have hneg_b : 0 ≤ (-u).b := by simp; omega
    have hneg_norm : PhiInt.norm (-u) = 1 := by rw [PhiInt.norm_neg, hu]
    rcases norm_one_signed_epsUnit_zpow_of_b_nonneg
      (-u).b.natAbs (-u) rfl hneg_b hneg_norm with ⟨m, hm | hm⟩
    · exact ⟨m, Or.inr (by simpa using congrArg Neg.neg hm)⟩
    · exact ⟨m, Or.inl (by simpa using congrArg Neg.neg hm)⟩

theorem epsNatMul_eq_pow_mul (n : Nat) (x : PhiInt) :
    epsNatMul n x = (((epsUnit ^ n : PhiIntˣ) : PhiInt) * x) := by
  induction n with
  | zero => simp [epsNatMul]
  | succ n ih =>
      rw [epsNatMul, epsMul_eq_mul, ih, pow_succ]
      simp only [Units.val_mul, epsUnit_val]
      ring

theorem epsInvNatMul_eq_pow_mul (n : Nat) (x : PhiInt) :
    epsInvNatMul n x = ((((epsUnit⁻¹) ^ n : PhiIntˣ) : PhiInt) * x) := by
  induction n with
  | zero => simp [epsInvNatMul]
  | succ n ih =>
      rw [epsInvNatMul, epsInvMul_eq_mul, ih, pow_succ]
      simp only [Units.val_mul, epsUnit_inv_val]
      ring

/-- The recursive coordinate action is multiplication by the corresponding
integral power of the fundamental unit. -/
theorem epsZPowMul_eq_zpow_mul (m : Int) (x : PhiInt) :
    epsZPowMul m x = (((epsUnit ^ m : PhiIntˣ) : PhiInt) * x) := by
  cases m with
  | ofNat n => simpa [epsZPowMul] using epsNatMul_eq_pow_mul n x
  | negSucc n =>
      simpa [epsZPowMul, zpow_negSucc] using epsInvNatMul_eq_pow_mul (n + 1) x

theorem epsZPowMul_add (m n : Int) (x : PhiInt) :
    epsZPowMul (m + n) x = epsZPowMul m (epsZPowMul n x) := by
  simp only [epsZPowMul_eq_zpow_mul]
  rw [zpow_add]
  simp only [Units.val_mul]
  ring

/-- A norm-one multiplier does not change the `sameIdeal` class. -/
theorem sameIdeal_of_norm_one_mul (u x : PhiInt) (hu : PhiInt.norm u = 1) :
    sameIdeal x (u * x) := by
  rcases norm_one_eq_sign_epsUnit_zpow u hu with ⟨m, hm | hm⟩
  · refine ⟨m, false, ?_⟩
    change u * x = epsZPowMul m x
    rw [epsZPowMul_eq_zpow_mul, ← hm]
  · refine ⟨m, true, ?_⟩
    change u * x = -(epsZPowMul m x)
    rw [epsZPowMul_eq_zpow_mul, hm]
    ring

/-- The associate relation is equivalently multiplication by an integral
norm-one element.  This form makes its equivalence properties immediate. -/
theorem sameIdeal_iff_exists_norm_one_mul (x y : PhiInt) :
    sameIdeal x y ↔
      ∃ u : PhiInt, PhiInt.norm u = 1 ∧ y = u * x := by
  constructor
  · rintro ⟨m, negative, hrel⟩
    cases negative with
    | false =>
        refine ⟨epsZPowMul m 1, ?_, ?_⟩
        · rw [norm_epsZPowMul]
          rfl
        · change y = epsZPowMul m 1 * x
          rw [hrel, epsZPowMul_eq_zpow_mul, epsZPowMul_eq_zpow_mul]
          simp
    | true =>
        refine ⟨-(epsZPowMul m 1), ?_, ?_⟩
        · rw [PhiInt.norm_neg]
          rw [norm_epsZPowMul]
          rfl
        · change y = -(epsZPowMul m 1) * x
          rw [hrel, epsZPowMul_eq_zpow_mul, epsZPowMul_eq_zpow_mul]
          simp
  · rintro ⟨u, hu, rfl⟩
    exact sameIdeal_of_norm_one_mul u x hu

theorem sameIdeal_refl (x : PhiInt) : sameIdeal x x := by
  rw [sameIdeal_iff_exists_norm_one_mul]
  exact ⟨1, by rfl, by simp⟩

theorem sameIdeal_symm {x y : PhiInt} (h : sameIdeal x y) : sameIdeal y x := by
  rw [sameIdeal_iff_exists_norm_one_mul] at h ⊢
  rcases h with ⟨u, hu, rfl⟩
  refine ⟨PhiInt.star u, by rw [PhiInt.norm_star, hu], ?_⟩
  symm
  calc
    PhiInt.star u * (u * x) = (PhiInt.star u * u) * x := by ring
    _ = (PhiInt.mk (PhiInt.norm u) 0) * x := by
      rw [PhiInt.star_mul_eq_norm]
    _ = (PhiInt.mk 1 0) * x := by rw [hu]
    _ = x := by ext <;> simp

theorem sameIdeal_trans {x y z : PhiInt}
    (hxy : sameIdeal x y) (hyz : sameIdeal y z) : sameIdeal x z := by
  rw [sameIdeal_iff_exists_norm_one_mul] at hxy hyz ⊢
  rcases hxy with ⟨u, hu, rfl⟩
  rcases hyz with ⟨v, hv, rfl⟩
  refine ⟨v * u, ?_, by ring⟩
  rw [PhiInt.norm_mul, hu, hv]
  ring

theorem sameIdeal_star {x y : PhiInt} (h : sameIdeal x y) :
    sameIdeal (PhiInt.star x) (PhiInt.star y) := by
  rw [sameIdeal_iff_exists_norm_one_mul] at h ⊢
  rcases h with ⟨u, hu, rfl⟩
  refine ⟨PhiInt.star u, by rw [PhiInt.norm_star, hu], ?_⟩
  exact PhiInt.star_mul u x

/-- For a split prime, all elements of norm `-p` lie in the generator class
or in its conjugate class. -/
theorem norm_prime_two_sameIdeal_classes
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {t : ZMod p} (ht : (5 : ZMod p) = t ^ 2) {x y : PhiInt}
    (hxnorm : PhiInt.norm x = -(p : Int))
    (hynorm : PhiInt.norm y = -(p : Int)) :
    sameIdeal x y ∨ sameIdeal (PhiInt.star x) y := by
  rcases norm_prime_two_orbits hp hp10 ht hxnorm hynorm with
    ⟨u, hu, hy⟩ | ⟨u, hu, hy⟩
  · left
    rw [hy]
    exact sameIdeal_of_norm_one_mul u x hu
  · right
    rw [hy]
    exact sameIdeal_of_norm_one_mul u (PhiInt.star x) hu

end Ch10
end QseriesFormalization
