import QseriesFormalization.Ch10_IotaInvariant

/-!
# Ch10: Iota reflection

Conjugation reverses the Shintani sector label and acts as Frobenius on the
mod-2 residue, giving the affine reflection law for `iota`.
-/

namespace QseriesFormalization
namespace Ch10

def reflectedSectorCert (x : PhiInt) (c : SectorCert x) :
    SectorCert (PhiInt.star x) where
  δ := -c.δ - 1

@[simp] theorem reflectedSectorCert_delta (x : PhiInt) (c : SectorCert x) :
    (reflectedSectorCert x c).δ = -c.δ - 1 := rfl

theorem toF4_star_as_frobenius (x : PhiInt) :
    toF4 (PhiInt.star x) = ((toF4 x).1 + (toF4 x).2, (toF4 x).2) := by
  unfold toF4
  ext <;> simp [PhiInt.star]

theorem lambdaOf_star (x : PhiInt) (hx : toF4 x ≠ (0, 0)) :
    lambdaOf (PhiInt.star x) = 2 * lambdaOf x := by
  unfold lambdaOf
  rw [toF4_star_as_frobenius]
  exact discreteLog_star_eq_double (toF4 x) hx

theorem iota_reflection (x : PhiInt) (c : SectorCert x) (hx : toF4 x ≠ (0, 0)) :
    iotaCert (PhiInt.star x) (reflectedSectorCert x c) = -iotaCert x c - 1 := by
  unfold iotaCert
  simp only [reflectedSectorCert_delta, lambdaOf_star x hx]
  have h2 : (2 : ZMod 3) = -1 := by decide
  rw [h2]
  ring

end Ch10
end QseriesFormalization
