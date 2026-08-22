import QseriesFormalization.Ch10_NormTheta_Defs
import QseriesFormalization.Ch10_EmbeddingSigns
import Mathlib.Data.ZMod.Basic

/-!
# Ch10: Shintani sectors

This file records the boundary rays and determinant predicates for the three
Shintani sectors used in the iota invariant.  The sector label is carried as
data in `SectorCert`; no total sector-index function is introduced.
-/

namespace QseriesFormalization
namespace Ch10

def detPhi (u v : PhiInt) : Int := u.a * v.b - u.b * v.a

def shB0 : PhiInt := PhiInt.mk (-1) 2
def shB1 : PhiInt := PhiInt.mk 1 3
def shB2 : PhiInt := PhiInt.mk 4 7
def shB3 : PhiInt := PhiInt.mk 11 18

def InConeBetween (left right x : PhiInt) : Prop :=
  0 ≤ detPhi left x ∧ 0 < detPhi x right

def InSector0 (x : PhiInt) : Prop := InConeBetween shB0 shB1 x
def InSector1 (x : PhiInt) : Prop := InConeBetween shB1 shB2 x
def InSector2 (x : PhiInt) : Prop := InConeBetween shB2 shB3 x

def InSector (δ : ZMod 3) (x : PhiInt) : Prop :=
  if δ = 0 then InSector0 x else if δ = 1 then InSector1 x else InSector2 x

structure SectorCert (x : PhiInt) where
  δ : ZMod 3

theorem eps_maps_shB0_to_shB1 : PhiInt.eps * shB0 = shB1 := by
  ext <;> simp [PhiInt.eps, shB0, shB1]

theorem eps_maps_shB1_to_shB2 : PhiInt.eps * shB1 = shB2 := by
  ext <;> simp [PhiInt.eps, shB1, shB2]

theorem eps_maps_shB2_to_shB3 : PhiInt.eps * shB2 = shB3 := by
  ext <;> simp [PhiInt.eps, shB2, shB3]

theorem detPhi_eps_left (u v : PhiInt) :
    detPhi (PhiInt.eps * u) v =
      (u.a + u.b) * v.b - (u.a + 2 * u.b) * v.a := by
  simp only [detPhi, PhiInt.mul_a, PhiInt.mul_b, PhiInt.eps, PhiInt.mk_a, PhiInt.mk_b]
  ring

theorem detPhi_eps_right (u v : PhiInt) :
    detPhi u (PhiInt.eps * v) =
      u.a * (v.a + 2 * v.b) - u.b * (v.a + v.b) := by
  simp only [detPhi, PhiInt.mul_a, PhiInt.mul_b, PhiInt.eps, PhiInt.mk_a, PhiInt.mk_b]
  ring

theorem detPhi_eps_both (u v : PhiInt) :
    detPhi (PhiInt.eps * u) (PhiInt.eps * v) = detPhi u v := by
  simp [detPhi, PhiInt.eps]
  ring

theorem detPhi_star (u v : PhiInt) :
    detPhi (PhiInt.star u) (PhiInt.star v) = -detPhi u v := by
  simp [detPhi, PhiInt.star]
  ring

end Ch10
end QseriesFormalization
