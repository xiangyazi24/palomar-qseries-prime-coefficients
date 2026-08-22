import QseriesFormalization.Ch10_SplitPrime
import QseriesFormalization.Ch10_PhiIntBridge
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

/-!
# Ch10: Unconditional split-prime generators

This file constructs the generator required by `SplitPrimeCert` for every
prime congruent to one modulo ten.  The proof is the quadratic-form version of
Thue's lemma: quadratic reciprocity supplies a square root of five modulo the
prime, and a square pigeonhole grid supplies a short nonzero vector in the
kernel of the resulting linear form.
-/

namespace QseriesFormalization
namespace Ch10

/-- Five is a quadratic residue modulo every prime congruent to one modulo ten. -/
theorem five_isSquare_zmod_of_prime_mod10_one {p : Nat}
    (hp : Nat.Prime p) (hp10 : p % 10 = 1) :
    IsSquare (5 : ZMod p) := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp5 : p % 5 = 1 := by omega
  have hp_ne_two : p ≠ 2 := by omega
  apply (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one
    (p := 5) (q := p) (by norm_num) hp_ne_two).mp
  refine ⟨1, ?_⟩
  simpa using (ZMod.natCast_eq_natCast_iff' p 1 5).mpr (by omega)

/-- Completing the square bounds the discriminant-five norm on a square box. -/
theorem four_mul_abs_normForm_le_five_mul_sq
    {x y m : Int} (hx : |x| ≤ m) (hy : |y| ≤ m) :
    4 * |x ^ 2 + x * y - y ^ 2| ≤ 5 * m ^ 2 := by
  have hm : 0 ≤ m := le_trans (abs_nonneg x) hx
  have hx_prod : 0 ≤ (m - |x|) * (m + |x|) :=
    mul_nonneg (sub_nonneg.mpr hx) (add_nonneg hm (abs_nonneg x))
  have hy_prod : 0 ≤ (m - |y|) * (m + |y|) :=
    mul_nonneg (sub_nonneg.mpr hy) (add_nonneg hm (abs_nonneg y))
  have hx_sq : x ^ 2 ≤ m ^ 2 := by
    nlinarith [sq_abs x]
  have hy_sq : y ^ 2 ≤ m ^ 2 := by
    nlinarith [sq_abs y]
  have hu : 4 * (x ^ 2 + x * y - y ^ 2) ≤ 5 * m ^ 2 := by
    have hs : 0 ≤ (x - 2 * y) ^ 2 := sq_nonneg (x - 2 * y)
    nlinarith
  have hl : -(5 * m ^ 2) ≤ 4 * (x ^ 2 + x * y - y ^ 2) := by
    have hs : 0 ≤ (2 * x + y) ^ 2 := sq_nonneg (2 * x + y)
    nlinarith
  have habs : |4 * (x ^ 2 + x * y - y ^ 2)| ≤ 5 * m ^ 2 :=
    (abs_le.mpr ⟨hl, hu⟩)
  calc
    4 * |x ^ 2 + x * y - y ^ 2| =
        |4 * (x ^ 2 + x * y - y ^ 2)| := by norm_num [abs_mul]
    _ ≤ 5 * m ^ 2 := habs

/-- A nonzero short vector in the modular kernel used by Thue's lemma. -/
structure ShortKernelVector (p : Nat) (t : ZMod p) where
  x : Int
  y : Int
  nonzero : x ≠ 0 ∨ y ≠ 0
  abs_x_le : |x| ≤ (Nat.sqrt p : Int)
  abs_y_le : |y| ≤ (Nat.sqrt p : Int)
  kernel :
    (2 : ZMod p) * (x : ZMod p) +
      (1 - t) * (y : ZMod p) = 0

/-- Pigeonhole construction of a short kernel vector. -/
theorem exists_shortKernelVector (p : Nat) (t : ZMod p) (hp : 0 < p) :
    Nonempty (ShortKernelVector p t) := by
  letI : NeZero p := ⟨Nat.ne_of_gt hp⟩
  let m := Nat.sqrt p
  let f : Fin (m + 1) × Fin (m + 1) → ZMod p := fun q =>
    (2 : ZMod p) * (q.1.val : ZMod p) +
      (1 - t) * (q.2.val : ZMod p)
  have hcard :
      Fintype.card (ZMod p) <
        Fintype.card (Fin (m + 1) × Fin (m + 1)) := by
    simp only [ZMod.card, Fintype.card_prod, Fintype.card_fin]
    simpa [m, Nat.pow_two] using Nat.lt_succ_sqrt p
  rcases Fintype.exists_ne_map_eq_of_card_lt f hcard with
    ⟨u, v, huv, hf⟩
  let x : Int := (u.1.val : Int) - (v.1.val : Int)
  let y : Int := (u.2.val : Int) - (v.2.val : Int)
  have hnonzero : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h
    push Not at h
    apply huv
    apply Prod.ext
    · apply Fin.ext
      dsimp [x] at h
      omega
    · apply Fin.ext
      dsimp [y] at h
      omega
  have hux : (u.1.val : Int) ≤ (m : Int) := by
    exact_mod_cast Nat.le_of_lt_succ u.1.isLt
  have hvx : (v.1.val : Int) ≤ (m : Int) := by
    exact_mod_cast Nat.le_of_lt_succ v.1.isLt
  have huy : (u.2.val : Int) ≤ (m : Int) := by
    exact_mod_cast Nat.le_of_lt_succ u.2.isLt
  have hvy : (v.2.val : Int) ≤ (m : Int) := by
    exact_mod_cast Nat.le_of_lt_succ v.2.isLt
  have hx : |x| ≤ (m : Int) := by
    dsimp [x]
    rw [abs_le]
    constructor <;> omega
  have hy : |y| ≤ (m : Int) := by
    dsimp [y]
    rw [abs_le]
    constructor <;> omega
  have hkernel :
      (2 : ZMod p) * (x : ZMod p) +
        (1 - t) * (y : ZMod p) = 0 := by
    dsimp [x, y]
    push_cast
    dsimp [f] at hf
    linear_combination hf
  exact ⟨{
    x := x
    y := y
    nonzero := hnonzero
    abs_x_le := by simpa [m] using hx
    abs_y_le := by simpa [m] using hy
    kernel := hkernel
  }⟩

/-- The short modular kernel vector has norm divisible by the prime. -/
theorem prime_dvd_normForm_of_shortKernelVector
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {t : ZMod p} (ht : (5 : ZMod p) = t ^ 2)
    (v : ShortKernelVector p t) :
    (p : Int) ∣ v.x ^ 2 + v.x * v.y - v.y ^ 2 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hlinear :
      (2 : ZMod p) * (v.x : ZMod p) + (v.y : ZMod p) =
        t * (v.y : ZMod p) := by
    linear_combination v.kernel
  have hsquare :
      ((2 : ZMod p) * (v.x : ZMod p) + (v.y : ZMod p)) ^ 2 =
        (t * (v.y : ZMod p)) ^ 2 := by
    exact congrArg (fun z : ZMod p => z ^ 2) hlinear
  have hfour :
      (4 : ZMod p) *
        ((v.x ^ 2 + v.x * v.y - v.y ^ 2 : Int) : ZMod p) = 0 := by
    push_cast
    calc
      (4 : ZMod p) *
          ((v.x : ZMod p) ^ 2 + (v.x : ZMod p) * (v.y : ZMod p) -
            (v.y : ZMod p) ^ 2) =
          ((2 : ZMod p) * (v.x : ZMod p) + (v.y : ZMod p)) ^ 2 -
            5 * (v.y : ZMod p) ^ 2 := by ring
      _ = (t * (v.y : ZMod p)) ^ 2 - 5 * (v.y : ZMod p) ^ 2 := by
        rw [hsquare]
      _ = 0 := by rw [ht]; ring
  have hp_gt_four : 4 < p := by
    have hp_two_le := hp.two_le
    omega
  have hfour_ne : (4 : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ 4 :=
      (ZMod.natCast_eq_zero_iff 4 p).mp (by simpa using hzero)
    have := Nat.le_of_dvd (by norm_num : 0 < 4) hdiv
    omega
  have hnorm_mod :
      ((v.x ^ 2 + v.x * v.y - v.y ^ 2 : Int) : ZMod p) = 0 :=
    (mul_eq_zero.mp hfour).resolve_left hfour_ne
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd
    (v.x ^ 2 + v.x * v.y - v.y ^ 2) p).mp hnorm_mod

/-- The short vector is genuinely nonzero, hence so is its norm. -/
theorem normForm_ne_zero_of_shortKernelVector
    {p : Nat} {t : ZMod p} (v : ShortKernelVector p t) :
    v.x ^ 2 + v.x * v.y - v.y ^ 2 ≠ 0 := by
  intro hnorm
  let z : PhiInt := ⟨v.x, v.y⟩
  have hz_norm : PhiInt.norm z = 0 := by
    simpa [z, PhiInt.norm] using hnorm
  have hz : z = 0 := PhiInt.eq_zero_of_norm_eq_zero hz_norm
  have hx : v.x = 0 := by
    have := congrArg PhiInt.a hz
    simpa [z] using this
  have hy : v.y = 0 := by
    have := congrArg PhiInt.b hz
    simpa [z] using this
  rcases v.nonzero with hx0 | hy0
  · exact hx0 hx
  · exact hy0 hy

/-- The short-vector norm has absolute value strictly below twice the prime. -/
theorem abs_normForm_lt_two_mul_of_shortKernelVector
    {p : Nat} (hp : 0 < p) {t : ZMod p} (v : ShortKernelVector p t) :
    |v.x ^ 2 + v.x * v.y - v.y ^ 2| < 2 * (p : Int) := by
  have hbox := four_mul_abs_normForm_le_five_mul_sq
    v.abs_x_le v.abs_y_le
  have hsqrt_nat : (Nat.sqrt p) ^ 2 ≤ p := Nat.sqrt_le' p
  have hsqrt_int : ((Nat.sqrt p : Int) ^ 2) ≤ (p : Int) := by
    exact_mod_cast hsqrt_nat
  have hp_int : 0 < (p : Int) := by exact_mod_cast hp
  nlinarith

/-- A nonzero multiple of `p` of size below `2p` is `p` or `-p`. -/
theorem eq_pos_or_neg_of_dvd_abs_lt_two_mul
    {p : Nat} {q : Int} (hp : 0 < p) (hdiv : (p : Int) ∣ q)
    (hq : q ≠ 0) (hlt : |q| < 2 * (p : Int)) :
    q = (p : Int) ∨ q = -(p : Int) := by
  rcases hdiv with ⟨k, hk⟩
  have hp_int : 0 < (p : Int) := by exact_mod_cast hp
  have hk_ne : k ≠ 0 := by
    intro hk0
    apply hq
    rw [hk, hk0]
    simp
  have hk_abs_lt : |k| < 2 := by
    rw [hk, abs_mul, abs_of_nonneg (le_of_lt hp_int)] at hlt
    nlinarith [abs_nonneg k]
  have hk_cases : k = 1 ∨ k = -1 := by
    rcases le_total 0 k with hk_nonneg | hk_nonpos
    · left
      rw [abs_of_nonneg hk_nonneg] at hk_abs_lt
      omega
    · right
      rw [abs_of_nonpos hk_nonpos] at hk_abs_lt
      omega
  rcases hk_cases with rfl | rfl
  · left; simpa using hk
  · right; simpa using hk

/-- Every prime congruent to one modulo ten has a norm-`±p` generator. -/
theorem exists_splitPrimeGenerator {p : Nat}
    (hp : Nat.Prime p) (hp10 : p % 10 = 1) :
    ∃ π : PhiInt,
      PhiInt.norm π = (p : Int) ∨ PhiInt.norm π = -(p : Int) := by
  rcases five_isSquare_zmod_of_prime_mod10_one hp hp10 with ⟨t, ht⟩
  rcases exists_shortKernelVector p t hp.pos with ⟨v⟩
  let π : PhiInt := ⟨v.x, v.y⟩
  refine ⟨π, ?_⟩
  have hdiv := prime_dvd_normForm_of_shortKernelVector hp hp10
    (by simpa [pow_two] using ht) v
  have hne := normForm_ne_zero_of_shortKernelVector v
  have hlt := abs_normForm_lt_two_mul_of_shortKernelVector hp.pos v
  simpa [π, PhiInt.norm] using
    eq_pos_or_neg_of_dvd_abs_lt_two_mul hp.pos hdiv hne hlt

@[simp] theorem PhiInt.norm_phi : PhiInt.norm PhiInt.phi = -1 := by
  rfl

/-- The sign of the generator can be fixed to `-p`: multiplication by `phi`
changes the norm sign and preserves integrality. -/
theorem exists_negNormPrimeGenerator {p : Nat}
    (hp : Nat.Prime p) (hp10 : p % 10 = 1) :
    ∃ x : PhiInt, PhiInt.norm x = -(p : Int) := by
  rcases exists_splitPrimeGenerator hp hp10 with ⟨π, hnorm | hnorm⟩
  · refine ⟨PhiInt.phi * π, ?_⟩
    rw [PhiInt.norm_mul, PhiInt.norm_phi, hnorm]
    ring
  · exact ⟨π, hnorm⟩

/-- Unconditional existence of the split-prime certificate used downstream. -/
theorem exists_splitPrimeCert {p : Nat}
    (hp : Nat.Prime p) (hp10 : p % 10 = 1) :
    Nonempty (SplitPrimeCert p) := by
  rcases exists_splitPrimeGenerator hp hp10 with ⟨π, hnorm⟩
  exact ⟨SplitPrimeCert.ofGenerator p π hp hp10 hnorm⟩

end Ch10
end QseriesFormalization
