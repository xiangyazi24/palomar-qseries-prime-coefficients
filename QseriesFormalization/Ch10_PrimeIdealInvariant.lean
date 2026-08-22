import QseriesFormalization.Ch10_LNormalization
import Mathlib.Tactic

/-!
# Ch10: Same-ideal invariance of the geometric iota class

For norm-negative generators of an admissible split prime, the integral
geometric normalization changes by exactly the exponent of the intervening
norm-one unit.  The finite logarithm changes by the same exponent, so their
difference is independent of the chosen generator in a `sameIdeal` class.
-/

namespace QseriesFormalization
namespace Ch10

/-- The geometric `iotaCert` is independent of the norm-`-p` generator inside
one `sameIdeal` class. -/
theorem geometric_iota_eq_of_sameIdeal
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x y : PhiInt} (hx : PhiInt.norm x = -(p : Int))
    (hxy : sameIdeal x y)
    (c : GeometricSectorCert x) (d : GeometricSectorCert y) :
    iotaCert y d.toSectorCert = iotaCert x c.toSectorCert := by
  rcases hxy with ⟨m, negative, hy⟩
  cases negative with
  | false =>
      change y = epsZPowMul m x at hy
      subst y
      let e : GeometricSectorCert (epsZPowMul m x) := {
        lift := c.lift + m
        normalized := by
          rw [← epsZPowMul_add]
          have hsum : -(c.lift + m) + m = -c.lift := by ring
          rw [hsum]
          exact c.normalized
      }
      have hd : d.lift = c.lift + m := by
        simpa [e] using d.lift_unique e
      unfold iotaCert
      change (d.lift : ZMod 3) - lambdaOf (epsZPowMul m x) =
        (c.lift : ZMod 3) - lambdaOf x
      rw [hd, lambdaOf_epsZPowMul_of_norm_eq_neg_split_prime hp hp10 hx]
      push_cast
      ring
  | true =>
      change y = -(epsZPowMul m x) at hy
      subst y
      let e : GeometricSectorCert (-(epsZPowMul m x)) := {
        lift := c.lift + m
        normalized := by
          rw [epsZPowMul_neg, sameWindowSign_neg_iff, ← epsZPowMul_add]
          have hsum : -(c.lift + m) + m = -c.lift := by ring
          rw [hsum]
          exact c.normalized
      }
      have hd : d.lift = c.lift + m := by
        simpa [e] using d.lift_unique e
      unfold iotaCert
      change (d.lift : ZMod 3) - lambdaOf (-(epsZPowMul m x)) =
        (c.lift : ZMod 3) - lambdaOf x
      rw [hd, lambdaOf_neg,
        lambdaOf_epsZPowMul_of_norm_eq_neg_split_prime hp hp10 hx]
      push_cast
      ring

end Ch10
end QseriesFormalization
