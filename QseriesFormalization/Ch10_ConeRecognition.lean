import QseriesFormalization.Ch10_PhiIntBridge

/-!
# Ch10: Integral cone recognition

The two linear forms in this file are the integral avatars of the two
archimedean comparisons used in the paper.  On `beta k r` they are respectively
`5 * r + 1` and `10 * k + 1`.
-/

namespace QseriesFormalization
namespace Ch10

/-- The field trace of `a + b * phi`, written in integral coordinates. -/
def Tr (x : PhiInt) : Int := 2 * x.a + x.b

/-- The second integral window coordinate. -/
def windowComp (x : PhiInt) : Int := x.b - 3 * x.a

/-- Membership in either atom cone. -/
def InCones (k r : Int) : Prop := InACone k r ∨ InDCone k r

theorem trace_beta (k r : Int) : Tr (beta k r) = 5 * r + 1 := by
  simp [Tr, beta]
  ring

theorem windowComp_beta (k r : Int) : windowComp (beta k r) = 10 * k + 1 := by
  simp [windowComp, beta]
  ring

theorem phi_pow_two : PhiInt.phi ^ 2 = PhiInt.mk 1 1 := by
  ext <;> simp [PhiInt.phi, pow_two]

theorem phi_pow_four : PhiInt.phi ^ 4 = PhiInt.mk 2 3 := by
  calc
    PhiInt.phi ^ 4 = (PhiInt.phi ^ 2) * (PhiInt.phi ^ 2) := by ring
    _ = PhiInt.mk 1 1 * PhiInt.mk 1 1 := by rw [phi_pow_two]
    _ = PhiInt.mk 2 3 := by ext <;> norm_num

/--
Integral form of
`sigma_1(beta) + phi^4 * sigma_2(beta) = -phi^2 * (10k+1)`.
-/
theorem paired_embedding_identity (k r : Int) :
    beta k r + (PhiInt.phi ^ 4) * PhiInt.star (beta k r) =
      -(PhiInt.phi ^ 2) * ((10 * k + 1 : Int) : PhiInt) := by
  rw [phi_pow_four, phi_pow_two]
  have h : ((10 * k + 1 : Int) : PhiInt) = PhiInt.mk (10 * k + 1) 0 := rfl
  rw [h]
  ext <;> simp [beta, PhiInt.star] <;> ring

theorem inACone_iff_coordinate_signs (k r : Int) :
    InACone k r ↔
      1 ≤ Tr (beta k r) ∧ 1 ≤ windowComp (beta k r) := by
  rw [trace_beta, windowComp_beta]
  simp only [InACone]
  omega

theorem inDCone_iff_coordinate_signs (k r : Int) :
    InDCone k r ↔
      Tr (beta k r) ≤ -1 ∧ windowComp (beta k r) ≤ -1 := by
  rw [trace_beta, windowComp_beta]
  simp only [InDCone]
  omega

theorem inCones_iff_coordinate_signs (k r : Int) :
    InCones k r ↔
      (1 ≤ Tr (beta k r) ∧ 1 ≤ windowComp (beta k r)) ∨
      (Tr (beta k r) ≤ -1 ∧ windowComp (beta k r) ≤ -1) := by
  simp only [InCones, inACone_iff_coordinate_signs,
    inDCone_iff_coordinate_signs]

end Ch10
end QseriesFormalization
