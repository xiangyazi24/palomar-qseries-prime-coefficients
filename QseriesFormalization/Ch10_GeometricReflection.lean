import QseriesFormalization.Ch10_LNormalization
import Mathlib.Tactic

/-!
# Ch10: Geometric normalization under conjugation

Conjugation reverses the integral unit exponent.  The additional multiplication
by `eps` swaps the two strict window coordinates, so a geometric sector lift
`ell` is carried to the lift `-ell - 1` used by `reflectedSectorCert`.
-/

namespace QseriesFormalization
namespace Ch10

theorem PhiInt.star_epsMul (x : PhiInt) :
    PhiInt.star (epsMul x) = epsInvMul (PhiInt.star x) := by
  ext <;> simp [PhiInt.star, epsMul, epsInvMul] <;> ring

theorem PhiInt.star_epsInvMul (x : PhiInt) :
    PhiInt.star (epsInvMul x) = epsMul (PhiInt.star x) := by
  ext <;> simp [PhiInt.star, epsMul, epsInvMul] <;> ring

theorem PhiInt.star_epsNatMul (n : Nat) (x : PhiInt) :
    PhiInt.star (epsNatMul n x) = epsInvNatMul n (PhiInt.star x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [epsNatMul, epsInvNatMul, PhiInt.star_epsMul, ih]

theorem PhiInt.star_epsInvNatMul (n : Nat) (x : PhiInt) :
    PhiInt.star (epsInvNatMul n x) = epsNatMul n (PhiInt.star x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [epsInvNatMul, epsNatMul, PhiInt.star_epsInvMul, ih]

/-- Conjugation reverses the integral fundamental-unit exponent. -/
theorem PhiInt.star_epsZPowMul (m : Int) (x : PhiInt) :
    PhiInt.star (epsZPowMul m x) = epsZPowMul (-m) (PhiInt.star x) := by
  cases m with
  | ofNat n =>
      cases n with
      | zero => rfl
      | succ n =>
          rw [show -(Int.ofNat (n + 1)) = Int.negSucc n by
            rw [Int.negSucc_eq, Int.ofNat_eq_natCast]
            push_cast
            ring]
          simpa [epsZPowMul] using PhiInt.star_epsNatMul (n + 1) x
  | negSucc n =>
      rw [show -(Int.negSucc n) = Int.ofNat (n + 1) by
        rw [Int.negSucc_eq, Int.ofNat_eq_natCast]
        push_cast
        ring]
      simpa [epsZPowMul] using PhiInt.star_epsInvNatMul (n + 1) x

theorem Tr_epsMul_star (x : PhiInt) :
    Tr (epsMul (PhiInt.star x)) = -windowComp x := by
  simp [Tr, windowComp, epsMul, PhiInt.star]
  ring

theorem windowComp_epsMul_star (x : PhiInt) :
    windowComp (epsMul (PhiInt.star x)) = -Tr x := by
  simp [Tr, windowComp, epsMul, PhiInt.star]
  ring

/-- Conjugation followed by `eps` swaps the two strict window coordinates. -/
theorem sameWindowSign_epsMul_star {x : PhiInt}
    (h : SameWindowSign x) : SameWindowSign (epsMul (PhiInt.star x)) := by
  simp only [SameWindowSign] at h ⊢
  rw [Tr_epsMul_star, windowComp_epsMul_star]
  rcases h with h | h
  · exact Or.inr ⟨by omega, by omega⟩
  · exact Or.inl ⟨by omega, by omega⟩

/-- The geometric certificate canonically induced on the conjugate element. -/
def GeometricSectorCert.reflected {x : PhiInt}
    (c : GeometricSectorCert x) : GeometricSectorCert (PhiInt.star x) where
  lift := -c.lift - 1
  normalized := by
    have hsame := sameWindowSign_epsMul_star c.normalized
    have heq :
        epsZPowMul (-(-c.lift - 1)) (PhiInt.star x) =
          epsMul (PhiInt.star (epsZPowMul (-c.lift) x)) := by
      rw [PhiInt.star_epsZPowMul]
      rw [show -(-c.lift) = c.lift by ring]
      rw [show -(-c.lift - 1) = 1 + c.lift by ring]
      rw [epsZPowMul_add]
      simp [epsZPowMul, epsNatMul]
    rw [heq]
    exact hsame

@[simp] theorem GeometricSectorCert.reflected_lift {x : PhiInt}
    (c : GeometricSectorCert x) : c.reflected.lift = -c.lift - 1 := rfl

/-- The integral geometric reflection realizes the pre-existing finite sector
reflection exactly, not merely up to an unconstrained label. -/
theorem GeometricSectorCert.toSectorCert_reflected {x : PhiInt}
    (c : GeometricSectorCert x) :
    c.reflected.toSectorCert = reflectedSectorCert x c.toSectorCert := by
  change
    ({ δ := ((-c.lift - 1 : Int) : ZMod 3) } :
      SectorCert (PhiInt.star x)) =
    ({ δ := -(c.lift : ZMod 3) - 1 } :
      SectorCert (PhiInt.star x))
  rw [SectorCert.mk.injEq]
  push_cast
  ring

end Ch10
end QseriesFormalization
