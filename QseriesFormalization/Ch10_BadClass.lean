import QseriesFormalization.Ch10_IotaReflection

/-!
# Ch10: Bad-class obstruction

The mod-3 reflection law rules out the possibility that both conjugate
generators lie in the bad iota class `2`.
-/

namespace QseriesFormalization
namespace Ch10

def BadIota (x : PhiInt) (c : SectorCert x) : Prop := iotaCert x c = 2

def Contributes (x : PhiInt) (c : SectorCert x) : Prop := iotaCert x c ≠ 2

def ConjugateBadPair (x : PhiInt) (c : SectorCert x) : Prop :=
  BadIota x c ∧ BadIota (PhiInt.star x) (reflectedSectorCert x c)

theorem bad_class_two_impossible :
    (2 : ZMod 3) + (2 : ZMod 3) ≠ (-1 : ZMod 3) := by
  decide

theorem iota_star_eq_zero_of_iota_eq_two
    (x : PhiInt) (c : SectorCert x) (hx : toF4 x ≠ (0, 0))
    (h : iotaCert x c = 2) :
    iotaCert (PhiInt.star x) (reflectedSectorCert x c) = 0 := by
  rw [iota_reflection x c hx, h]
  decide

theorem not_both_bad_iota
    (x : PhiInt) (c : SectorCert x) (hx : toF4 x ≠ (0, 0)) :
    ¬ ConjugateBadPair x c := by
  intro hbad
  rcases hbad with ⟨hx_bad, hstar_bad⟩
  have hstar_zero := iota_star_eq_zero_of_iota_eq_two x c hx hx_bad
  rw [BadIota] at hstar_bad
  rw [hstar_bad] at hstar_zero
  exact (by decide : ¬ ((2 : ZMod 3) = 0)) hstar_zero

theorem at_least_one_contributes
    (x : PhiInt) (c : SectorCert x) (hx : toF4 x ≠ (0, 0)) :
    Contributes x c ∨ Contributes (PhiInt.star x) (reflectedSectorCert x c) := by
  by_cases h : BadIota x c
  · right
    intro hstar
    exact not_both_bad_iota x c hx ⟨h, hstar⟩
  · left
    exact h

theorem prime_intro_mod3_obstruction
    (x : PhiInt) (c : SectorCert x) (hx : toF4 x ≠ (0, 0)) :
    ¬ (BadIota x c ∧ BadIota (PhiInt.star x) (reflectedSectorCert x c)) :=
  not_both_bad_iota x c hx

end Ch10
end QseriesFormalization
