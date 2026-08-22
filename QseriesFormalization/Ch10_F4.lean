import QseriesFormalization.Ch10_NormTheta_Defs
import Mathlib.Data.ZMod.Basic

/-!
# Ch10: Arithmetic modulo 2 in `Z[phi]`

The quotient `Z[phi] / 2` is represented by the coefficient pair
`ZMod 2 x ZMod 2`.  The unit `eps = 1 + phi` has order three on the
nonzero elements, and the lattice condition `InL` excludes the
`phi + 1` residue class.
-/

namespace QseriesFormalization
namespace Ch10

def toF4 (x : PhiInt) : ZMod 2 × ZMod 2 :=
  (↑x.a, ↑x.b)

def discreteLog (x : ZMod 2 × ZMod 2) : ZMod 3 :=
  if x = (1, 0) then 0
  else if x = (1, 1) then 1
  else if x = (0, 1) then 2
  else 0

private theorem intCast_zmod2_eq_of_mod_eq (a b : Int) (h : a % 2 = b % 2) :
    (↑a : ZMod 2) = (↑b : ZMod 2) :=
  (ZMod.intCast_eq_intCast_iff' a b 2).2 h

theorem L_mod2_excludes_lambda1 (x : PhiInt) (hL : InL x) :
    discreteLog (toF4 x) = 0 ∨ discreteLog (toF4 x) = 2 := by
  rcases hL with ⟨m, hm⟩
  have hodd : (x.a + x.b) % 2 = 1 := by
    have hsum : x.a + x.b = 1 + 2 * (5 * m + 2 * x.a) := by
      omega
    rw [hsum]
    omega
  by_cases ha0 : x.a % 2 = 0
  · have hb1 : x.b % 2 = 1 := by
      omega
    have haZ : (↑x.a : ZMod 2) = 0 := by
      simpa using intCast_zmod2_eq_of_mod_eq x.a 0 (by omega)
    have hbZ : (↑x.b : ZMod 2) = 1 := by
      simpa using intCast_zmod2_eq_of_mod_eq x.b 1 (by omega)
    right
    unfold toF4
    rw [haZ, hbZ]
    decide
  · have ha1 : x.a % 2 = 1 := by
      omega
    have hb0 : x.b % 2 = 0 := by
      omega
    have haZ : (↑x.a : ZMod 2) = 1 := by
      simpa using intCast_zmod2_eq_of_mod_eq x.a 1 (by omega)
    have hbZ : (↑x.b : ZMod 2) = 0 := by
      simpa using intCast_zmod2_eq_of_mod_eq x.b 0 (by omega)
    left
    unfold toF4
    rw [haZ, hbZ]
    decide

theorem star_mod2_is_frobenius (x : PhiInt) :
    toF4 (PhiInt.star x) =
      ((↑(x.a + x.b) : ZMod 2), (↑(-x.b) : ZMod 2)) := by
  rfl

theorem discreteLog_star_eq_double :
    ∀ p : ZMod 2 × ZMod 2, p ≠ (0, 0) →
    discreteLog (p.1 + p.2, p.2) = 2 * discreteLog p := by
  rintro ⟨a, b⟩ _
  fin_cases a <;> fin_cases b <;> decide

/-! ### F₄ multiplication and discreteLog multiplicativity -/

def f4mul (p q : ZMod 2 × ZMod 2) : ZMod 2 × ZMod 2 :=
  (p.1 * q.1 + p.2 * q.2, p.1 * q.2 + p.2 * q.1 + p.2 * q.2)

theorem toF4_mul (x y : PhiInt) : toF4 (x * y) = f4mul (toF4 x) (toF4 y) := by
  ext
  · show (↑(x * y).a : ZMod 2) = ↑x.a * ↑y.a + ↑x.b * ↑y.b
    have : (x * y).a = x.a * y.a + x.b * y.b := rfl
    rw [this]; push_cast; ring
  · show (↑(x * y).b : ZMod 2) = ↑x.a * ↑y.b + ↑x.b * ↑y.a + ↑x.b * ↑y.b
    have : (x * y).b = x.a * y.b + x.b * y.a + x.b * y.b := rfl
    rw [this]; push_cast; ring

theorem discreteLog_f4mul (p q : ZMod 2 × ZMod 2)
    (hp : p ≠ (0, 0)) (hq : q ≠ (0, 0)) :
    discreteLog (f4mul p q) = discreteLog p + discreteLog q := by
  revert hp hq
  rcases p with ⟨a, b⟩; rcases q with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

theorem discreteLog_mul (x y : PhiInt)
    (hx : toF4 x ≠ (0, 0)) (hy : toF4 y ≠ (0, 0)) :
    discreteLog (toF4 (x * y)) = discreteLog (toF4 x) + discreteLog (toF4 y) := by
  rw [toF4_mul, discreteLog_f4mul _ _ hx hy]

theorem toF4_eps : toF4 PhiInt.eps = (1, 1) := rfl

theorem discreteLog_eps : discreteLog (toF4 PhiInt.eps) = 1 := by
  rw [toF4_eps]; decide

end Ch10
end QseriesFormalization
