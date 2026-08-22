import QseriesFormalization.Ch10_SectorNormalization
import QseriesFormalization.Ch10_SplitPrime
import Mathlib.Tactic

/-!
# Ch10: From geometric normalization to the affine lattice

This file formalizes the finite arithmetic heart of Paper 3's normalization
lemma.  After unit normalization into the signed fundamental window, one sign
has window coordinate `1` modulo five.  For that sign, membership in `L` is
exactly exclusion of the bad mod-two discrete-log class.
-/

namespace QseriesFormalization
namespace Ch10

theorem windowComp_sq_add_norm (x : PhiInt) :
    windowComp x ^ 2 + PhiInt.norm x =
      5 * x.a * (2 * x.a - x.b) := by
  simp [windowComp, PhiInt.norm]
  ring

theorem windowComp_sq_zmod5_eq_one_of_norm_eq_neg_split_prime
    {p : Nat} (hp10 : p % 10 = 1) {x : PhiInt}
    (hnorm : PhiInt.norm x = -(p : Int)) :
    ((windowComp x : Int) : ZMod 5) ^ 2 = 1 := by
  have hpcast : ((p : Nat) : ZMod 5) = 1 := by
    simpa using (ZMod.natCast_eq_natCast_iff' p 1 5).mpr (by omega)
  have h := congrArg (fun z : Int => (z : ZMod 5)) (windowComp_sq_add_norm x)
  push_cast at h
  rw [hnorm] at h
  norm_num at h
  have hfive : (5 : ZMod 5) = 0 := by decide
  simp only [hpcast, hfive, zero_mul] at h
  linear_combination h

/-- One of the two overall signs has the paper's ramified residue, represented
integrally by `windowComp = 1` modulo five. -/
theorem exists_sign_windowComp_zmod5_eq_one
    {p : Nat} (hp10 : p % 10 = 1) {x : PhiInt}
    (hnorm : PhiInt.norm x = -(p : Int)) :
    ∃ y : PhiInt, (y = x ∨ y = -x) ∧
      ((windowComp y : Int) : ZMod 5) = 1 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hsq :=
    windowComp_sq_zmod5_eq_one_of_norm_eq_neg_split_prime hp10 hnorm
  have hfac :
      (((windowComp x : Int) : ZMod 5) - 1) *
        (((windowComp x : Int) : ZMod 5) + 1) = 0 := by
    calc
      (((windowComp x : Int) : ZMod 5) - 1) *
          (((windowComp x : Int) : ZMod 5) + 1) =
          ((windowComp x : Int) : ZMod 5) ^ 2 - 1 := by ring
      _ = 0 := by rw [hsq]; ring
  rcases mul_eq_zero.mp hfac with hplus | hminus
  · refine ⟨x, Or.inl rfl, sub_eq_zero.mp hplus⟩
  · refine ⟨-x, Or.inr rfl, ?_⟩
    have hx : ((windowComp x : Int) : ZMod 5) = -1 := by
      calc
        ((windowComp x : Int) : ZMod 5) =
            (((windowComp x : Int) : ZMod 5) + 1) - 1 := by ring
        _ = -1 := by rw [hminus]; ring
    have hwindow_neg : windowComp (-x) = -windowComp x := by
      simp [windowComp]
      ring
    rw [hwindow_neg]
    push_cast
    rw [hx]
    norm_num

private theorem intCast_zmod2_eq_of_mod_eq (a b : Int)
    (h : a % 2 = b % 2) : (a : ZMod 2) = (b : ZMod 2) :=
  (ZMod.intCast_eq_intCast_iff' a b 2).2 h

/-- On a nonzero `F4` residue, avoiding discrete-log class one is exactly
oddness of the integral window coordinate. -/
theorem lambdaOf_ne_one_iff_windowComp_mod2_one
    (x : PhiInt) (hx : toF4 x ≠ (0, 0)) :
    lambdaOf x ≠ 1 ↔ windowComp x % 2 = 1 := by
  by_cases ha0 : x.a % 2 = 0
  · by_cases hb0 : x.b % 2 = 0
    · exfalso
      apply hx
      ext
      · simpa [toF4] using intCast_zmod2_eq_of_mod_eq x.a 0 ha0
      · simpa [toF4] using intCast_zmod2_eq_of_mod_eq x.b 0 hb0
    · have hb1 : x.b % 2 = 1 := by omega
      have haZ : (x.a : ZMod 2) = 0 := by
        simpa using intCast_zmod2_eq_of_mod_eq x.a 0 ha0
      have hbZ : (x.b : ZMod 2) = 1 := by
        simpa using intCast_zmod2_eq_of_mod_eq x.b 1 hb1
      have hlambda : lambdaOf x = 2 := by
        unfold lambdaOf toF4 discreteLog
        rw [haZ, hbZ]
        decide
      have hwindow : windowComp x % 2 = 1 := by
        simp only [windowComp]
        omega
      rw [hlambda, hwindow]
      decide
  · have ha1 : x.a % 2 = 1 := by omega
    by_cases hb0 : x.b % 2 = 0
    · have haZ : (x.a : ZMod 2) = 1 := by
        simpa using intCast_zmod2_eq_of_mod_eq x.a 1 ha1
      have hbZ : (x.b : ZMod 2) = 0 := by
        simpa using intCast_zmod2_eq_of_mod_eq x.b 0 hb0
      have hlambda : lambdaOf x = 0 := by
        unfold lambdaOf toF4 discreteLog
        rw [haZ, hbZ]
        decide
      have hwindow : windowComp x % 2 = 1 := by
        simp only [windowComp]
        omega
      rw [hlambda, hwindow]
      decide
    · have hb1 : x.b % 2 = 1 := by omega
      have haZ : (x.a : ZMod 2) = 1 := by
        simpa using intCast_zmod2_eq_of_mod_eq x.a 1 ha1
      have hbZ : (x.b : ZMod 2) = 1 := by
        simpa using intCast_zmod2_eq_of_mod_eq x.b 1 hb1
      have hlambda : lambdaOf x = 1 := by
        unfold lambdaOf toF4 discreteLog
        rw [haZ, hbZ]
        decide
      have hwindow : windowComp x % 2 = 0 := by
        simp only [windowComp]
        omega
      rw [hlambda, hwindow]
      decide

/-- With the ramified mod-five sign fixed, the affine lattice condition is
exactly the two good mod-two discrete-log classes. -/
theorem mem_L_iff_lambdaOf_ne_one_of_windowComp_zmod5
    (x : PhiInt) (hx : toF4 x ≠ (0, 0))
    (h5 : ((windowComp x : Int) : ZMod 5) = 1) :
    InL x ↔ lambdaOf x ≠ 1 := by
  constructor
  · intro hL
    rcases L_mod2_excludes_lambda1 x hL with h | h
    · unfold lambdaOf
      rw [h]
      decide
    · unfold lambdaOf
      rw [h]
      decide
  · intro hlambda
    have h2mod : windowComp x % 2 = 1 :=
      (lambdaOf_ne_one_iff_windowComp_mod2_one x hx).mp hlambda
    have h5zero : (((windowComp x - 1 : Int) : ZMod 5)) = 0 := by
      push_cast
      rw [h5]
      norm_num
    have h5dvd : (5 : Int) ∣ windowComp x - 1 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (windowComp x - 1) 5).mp h5zero
    have h2dvd : (2 : Int) ∣ windowComp x - 1 := by
      use (windowComp x - 1) / 2
      omega
    rcases h5dvd with ⟨u, hu⟩
    rcases h2dvd with ⟨v, hv⟩
    have hu_even : u % 2 = 0 := by omega
    refine ⟨u / 2, ?_⟩
    simp only [windowComp] at *
    omega

theorem lambdaOf_epsInvMul_of_norm_eq_neg_split_prime
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int)) :
    lambdaOf (epsInvMul x) = lambdaOf x - 1 := by
  have hinvnorm : PhiInt.norm (epsInvMul x) = -(p : Int) := by
    rw [norm_epsInvMul, hnorm]
  have hinv2 : toF4 (epsInvMul x) ≠ (0, 0) :=
    split_prime_mod2_nonzero hp hp10 (Or.inr hinvnorm)
  have hshift := lambdaOf_eps (epsInvMul x) hinv2
  rw [← epsMul_eq_mul, epsMul_epsInvMul] at hshift
  linear_combination -hshift

private theorem lambdaOf_epsNatMul_of_norm_eq_neg_split_prime
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int)) :
    ∀ n : Nat,
      lambdaOf (epsNatMul n x) = lambdaOf x + (n : ZMod 3) := by
  intro n
  induction n with
  | zero => simp [epsNatMul]
  | succ n ih =>
      have hiternorm : PhiInt.norm (epsNatMul n x) = -(p : Int) := by
        rw [norm_epsNatMul, hnorm]
      have hiter2 : toF4 (epsNatMul n x) ≠ (0, 0) :=
        split_prime_mod2_nonzero hp hp10 (Or.inr hiternorm)
      rw [epsNatMul, epsMul_eq_mul, lambdaOf_eps _ hiter2, ih]
      push_cast
      ring

private theorem lambdaOf_epsInvNatMul_of_norm_eq_neg_split_prime
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int)) :
    ∀ n : Nat,
      lambdaOf (epsInvNatMul n x) = lambdaOf x - (n : ZMod 3) := by
  intro n
  induction n with
  | zero => simp [epsInvNatMul]
  | succ n ih =>
      have hiternorm : PhiInt.norm (epsInvNatMul n x) = -(p : Int) := by
        rw [norm_epsInvNatMul, hnorm]
      rw [epsInvNatMul,
        lambdaOf_epsInvMul_of_norm_eq_neg_split_prime hp hp10 hiternorm, ih]
      push_cast
      ring

/-- The finite logarithm shifts by the same integral unit exponent as the
geometric sector label. -/
theorem lambdaOf_epsZPowMul_of_norm_eq_neg_split_prime
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int)) (m : Int) :
    lambdaOf (epsZPowMul m x) = lambdaOf x + (m : ZMod 3) := by
  cases m with
  | ofNat n =>
      simpa [epsZPowMul] using
        lambdaOf_epsNatMul_of_norm_eq_neg_split_prime hp hp10 hnorm n
  | negSucc n =>
      change lambdaOf (epsInvNatMul (n + 1) x) =
        lambdaOf x + ((Int.negSucc n : Int) : ZMod 3)
      rw [lambdaOf_epsInvNatMul_of_norm_eq_neg_split_prime hp hp10 hnorm]
      push_cast
      ring

/-- The fully normalized representative used by the atom construction. -/
structure OrientedSectorNormalization {p : Nat} (x : PhiInt)
    (c : GeometricSectorCert x) where
  oriented : PhiInt
  eq_normalized_or_neg :
    oriented = epsZPowMul (-c.lift) x ∨
      oriented = -(epsZPowMul (-c.lift) x)
  window_mod5 : ((windowComp oriented : Int) : ZMod 5) = 1

theorem OrientedSectorNormalization.oriented_unique
    {p : Nat} {x : PhiInt} {c : GeometricSectorCert x}
    (o₁ o₂ : OrientedSectorNormalization (p := p) x c) :
    o₁.oriented = o₂.oriented := by
  let y := epsZPowMul (-c.lift) x
  have hwindow_neg : ∀ z : PhiInt,
      ((windowComp (-z) : Int) : ZMod 5) =
        -((windowComp z : Int) : ZMod 5) := by
    intro z
    have h : windowComp (-z) = -windowComp z := by
      simp [windowComp]
      ring
    rw [h]
    push_cast
    rfl
  rcases o₁.eq_normalized_or_neg with h₁ | h₁ <;>
    rcases o₂.eq_normalized_or_neg with h₂ | h₂
  · rw [h₁, h₂]
  · have hw₁ : ((windowComp y : Int) : ZMod 5) = 1 := by
      simpa [y, h₁] using o₁.window_mod5
    have hw₂ : -((windowComp y : Int) : ZMod 5) = 1 := by
      simpa [y, h₂, hwindow_neg] using o₂.window_mod5
    rw [hw₁] at hw₂
    exact ((by decide : (-1 : ZMod 5) ≠ 1) hw₂).elim
  · have hw₁ : -((windowComp y : Int) : ZMod 5) = 1 := by
      simpa [y, h₁, hwindow_neg] using o₁.window_mod5
    have hw₂ : ((windowComp y : Int) : ZMod 5) = 1 := by
      simpa [y, h₂] using o₂.window_mod5
    rw [hw₂] at hw₁
    exact ((by decide : (-1 : ZMod 5) ≠ 1) hw₁).elim
  · rw [h₁, h₂]

theorem exists_orientedSectorNormalization
    {p : Nat} (hp10 : p % 10 = 1) {x : PhiInt}
    (hnorm : PhiInt.norm x = -(p : Int)) (c : GeometricSectorCert x) :
    Nonempty (OrientedSectorNormalization (p := p) x c) := by
  have hnormed :
      PhiInt.norm (epsZPowMul (-c.lift) x) = -(p : Int) := by
    rw [norm_epsZPowMul, hnorm]
  rcases exists_sign_windowComp_zmod5_eq_one hp10 hnormed with
    ⟨y, hy, hy5⟩
  exact ⟨⟨y, hy, hy5⟩⟩

theorem OrientedSectorNormalization.norm_eq_neg_prime
    {p : Nat} {x : PhiInt} {c : GeometricSectorCert x}
    (o : OrientedSectorNormalization (p := p) x c)
    (hnorm : PhiInt.norm x = -(p : Int)) :
    PhiInt.norm o.oriented = -(p : Int) := by
  rcases o.eq_normalized_or_neg with h | h
  · rw [h, norm_epsZPowMul, hnorm]
  · rw [h, PhiInt.norm_neg, norm_epsZPowMul, hnorm]

theorem OrientedSectorNormalization.sameWindowSign
    {p : Nat} {x : PhiInt} {c : GeometricSectorCert x}
    (o : OrientedSectorNormalization (p := p) x c) :
    SameWindowSign o.oriented := by
  rcases o.eq_normalized_or_neg with h | h
  · simpa [h] using c.normalized
  · rw [h, sameWindowSign_neg_iff]
    exact c.normalized

theorem OrientedSectorNormalization.lambda_eq_neg_iota
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    {c : GeometricSectorCert x}
    (o : OrientedSectorNormalization (p := p) x c) :
    lambdaOf o.oriented = -iotaCert x c.toSectorCert := by
  have hshift :=
    lambdaOf_epsZPowMul_of_norm_eq_neg_split_prime hp hp10 hnorm (-c.lift)
  rcases o.eq_normalized_or_neg with h | h
  · rw [h, hshift]
    unfold iotaCert GeometricSectorCert.toSectorCert
    push_cast
    ring
  · rw [h, lambdaOf_neg, hshift]
    unfold iotaCert GeometricSectorCert.toSectorCert
    push_cast
    ring

/-- Source-faithful normalization lemma: a geometrically determined prime
class contributes exactly when its normalized, mod-five-oriented element lies
in the affine atom lattice. -/
theorem contributes_iff_oriented_mem_L
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    {c : GeometricSectorCert x}
    (o : OrientedSectorNormalization (p := p) x c) :
    Contributes x c.toSectorCert ↔ InL o.oriented := by
  have horient_norm := o.norm_eq_neg_prime hnorm
  have horient2 : toF4 o.oriented ≠ (0, 0) :=
    split_prime_mod2_nonzero hp hp10 (Or.inr horient_norm)
  rw [mem_L_iff_lambdaOf_ne_one_of_windowComp_zmod5
    o.oriented horient2 o.window_mod5]
  rw [o.lambda_eq_neg_iota hp hp10 hnorm]
  unfold Contributes
  have hfinite : ∀ z : ZMod 3, z ≠ 2 ↔ -z ≠ 1 := by decide
  exact hfinite (iotaCert x c.toSectorCert)

theorem inCones_of_sameWindowSign_beta {k r : Int}
    (h : SameWindowSign (beta k r)) : InCones k r := by
  rw [inCones_iff_coordinate_signs]
  simp only [SameWindowSign] at h
  rcases h with h | h
  · left; omega
  · right; omega

/-- A good geometric iota class produces an actual cone atom at the prime
coefficient level. -/
theorem exists_prime_cone_atom_of_contributes
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    {c : GeometricSectorCert x}
    (o : OrientedSectorNormalization (p := p) x c)
    (hcontrib : Contributes x c.toSectorCert) :
    ∃ k r : Int,
      beta k r = o.oriented ∧ InCones k r ∧
        E k r = ((p - 1) / 10 : Nat) := by
  have hL := (contributes_iff_oriented_mem_L hp hp10 hnorm o).mp hcontrib
  rcases exists_beta_of_mem_L o.oriented hL with ⟨k, r, hbeta⟩
  have hcones : InCones k r := by
    apply inCones_of_sameWindowSign_beta
    rw [hbeta]
    exact o.sameWindowSign
  have horient_norm := o.norm_eq_neg_prime hnorm
  have hlevel := norm_beta k r
  rw [hbeta, horient_norm] at hlevel
  refine ⟨k, r, hbeta, hcones, ?_⟩
  have hp_sub : p - 1 + 1 = p := by omega
  have hp_div : 10 * ((p - 1) / 10) = p - 1 := by omega
  exact_mod_cast (show E k r = ((p - 1) / 10 : Nat) by omega)

end Ch10
end QseriesFormalization
