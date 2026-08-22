import QseriesFormalization.Ch10_NormTheta_Defs

/-!
# Ch10: Decidable embedding signs

The sign tests are expressed entirely in the integer coordinates of
`Z[phi]`, avoiding a real-number embedding development.
-/

namespace QseriesFormalization
namespace Ch10

def normZ (x : PhiInt) : Int := x.a * x.a + x.a * x.b - x.b * x.b
def traceZ (x : PhiInt) : Int := 2 * x.a + x.b

def sigma1_pos (x : PhiInt) : Prop :=
  if normZ x < 0 then x.b > 0 else traceZ x > 0

def sigma2_neg (x : PhiInt) : Prop :=
  if normZ x < 0 then x.b > 0 else traceZ x < 0

def inHalfPlane (x : PhiInt) : Prop := normZ x < 0 ∧ x.b > 0

theorem beta_ACone_in_halfplane (k r : Int) (hk : 0 ≤ k) (hr : 0 ≤ r) :
    inHalfPlane (beta k r) := by
  unfold inHalfPlane
  constructor
  · simp [normZ, beta]
    ring_nf
    nlinarith [sq_nonneg k, sq_nonneg r, mul_nonneg hk hr]
  · simp [beta]
    omega

theorem star_swaps_halfplane (x : PhiInt) (h : inHalfPlane x) :
    normZ (PhiInt.star x) < 0 ∧ (PhiInt.star x).b < 0 := by
  rcases h with ⟨hn, hb⟩
  constructor
  · calc
      normZ (PhiInt.star x) = normZ x := by
        simp [normZ, PhiInt.star]
        ring
      _ < 0 := hn
  · simp [PhiInt.star]
    omega

theorem eps_maps_boundary : PhiInt.eps * PhiInt.mk (-1) 2 = PhiInt.mk 1 3 := by
  ext <;> simp [PhiInt.eps]

end Ch10
end QseriesFormalization
