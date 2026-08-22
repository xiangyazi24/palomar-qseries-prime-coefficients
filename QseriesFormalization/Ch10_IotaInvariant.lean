import QseriesFormalization.Ch10_ShintaniSector
import QseriesFormalization.Ch10_F4

/-!
# Ch10: Iota invariant

The Shintani sector label is supplied by `SectorCert`; the arithmetic part is
the discrete logarithm of the residue of `x` modulo 2.
-/

namespace QseriesFormalization
namespace Ch10

def lambdaOf (x : PhiInt) : ZMod 3 := discreteLog (toF4 x)

def iotaCert (x : PhiInt) (c : SectorCert x) : ZMod 3 := c.δ - lambdaOf x

theorem toF4_eps_mul (x : PhiInt) :
    toF4 (PhiInt.eps * x) = ((toF4 x).1 + (toF4 x).2, (toF4 x).1) := by
  have hb : (PhiInt.eps * x).b = x.a + 2 * x.b := by
    simp [PhiInt.eps]; ring
  unfold toF4
  ext
  · simp [PhiInt.eps]
  · rw [hb]
    exact (ZMod.intCast_eq_intCast_iff' (x.a + 2 * x.b) x.a 2).2 (by omega)

theorem discreteLog_eps_shift :
    ∀ p : ZMod 2 × ZMod 2, p ≠ (0, 0) →
      discreteLog (p.1 + p.2, p.1) = discreteLog p + 1 := by
  rintro ⟨a, b⟩ h
  fin_cases a <;> fin_cases b
  · exact absurd rfl h
  all_goals decide

theorem lambdaOf_eps (x : PhiInt) (hx : toF4 x ≠ (0, 0)) :
    lambdaOf (PhiInt.eps * x) = lambdaOf x + 1 := by
  unfold lambdaOf
  rw [toF4_eps_mul]
  exact discreteLog_eps_shift (toF4 x) hx

theorem iotaCert_eps_invariant
    (x : PhiInt) (c : SectorCert x) (cε : SectorCert (PhiInt.eps * x))
    (hδ : cε.δ = c.δ + 1) (hx : toF4 x ≠ (0, 0)) :
    iotaCert (PhiInt.eps * x) cε = iotaCert x c := by
  unfold iotaCert
  rw [hδ, lambdaOf_eps x hx]
  ring

theorem toF4_neg (x : PhiInt) : toF4 (-x) = toF4 x := by
  unfold toF4
  ext <;> simp

theorem lambdaOf_neg (x : PhiInt) : lambdaOf (-x) = lambdaOf x := by
  unfold lambdaOf
  rw [toF4_neg]

end Ch10
end QseriesFormalization
