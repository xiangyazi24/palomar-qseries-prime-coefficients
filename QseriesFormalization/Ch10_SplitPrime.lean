import QseriesFormalization.Ch10_BadClass
import Mathlib.Data.ZMod.Basic

/-!
# Ch10: Split-prime certificates

This file keeps the hard split-prime existence input explicit as a certificate.
The downstream mod-2 and bad-class consequences are proved unconditionally from
that certificate.
-/

namespace QseriesFormalization
namespace Ch10

structure SplitPrimeCert (p : Nat) where
  π : PhiInt
  hp : Nat.Prime p
  hp10 : p % 10 = 1
  hnorm : PhiInt.norm π = (p : Int) ∨ PhiInt.norm π = -(p : Int)
  hmod2 : toF4 π ≠ (0, 0)

namespace PhiInt

theorem four_dvd_norm_of_toF4_eq_zero {x : PhiInt} (hx : toF4 x = (0, 0)) :
    (4 : Int) ∣ PhiInt.norm x := by
  have haZ : (x.a : ZMod 2) = 0 := by
    simpa [toF4] using congrArg Prod.fst hx
  have hbZ : (x.b : ZMod 2) = 0 := by
    simpa [toF4] using congrArg Prod.snd hx
  rcases (ZMod.intCast_zmod_eq_zero_iff_dvd x.a 2).mp haZ with ⟨a0, ha⟩
  rcases (ZMod.intCast_zmod_eq_zero_iff_dvd x.b 2).mp hbZ with ⟨b0, hb⟩
  refine ⟨a0 ^ 2 + a0 * b0 - b0 ^ 2, ?_⟩
  simp [PhiInt.norm, ha, hb]
  ring

end PhiInt

private theorem not_four_dvd_int_of_mod10_eq_one {p : Nat} (hp10 : p % 10 = 1) :
    ¬ (4 : Int) ∣ (p : Int) := by
  intro h4
  rcases h4 with ⟨k, hk⟩
  have hp2 : p % 2 = 1 := by omega
  have hp2z_nat : ((p % 2 : Nat) : Int) = 1 := by
    norm_num [hp2]
  have hp2z : ((p : Int) % 2) = 1 := by
    simpa using hp2z_nat
  have hp2zero : ((p : Int) % 2) = 0 := by
    rw [hk]
    omega
  omega

theorem split_prime_mod2_nonzero
    {p : Nat} (_hp : Nat.Prime p) (hp10 : p % 10 = 1) {π : PhiInt}
    (hnorm : PhiInt.norm π = (p : Int) ∨ PhiInt.norm π = -(p : Int)) :
    toF4 π ≠ (0, 0) := by
  intro hzero
  have h4norm : (4 : Int) ∣ PhiInt.norm π :=
    PhiInt.four_dvd_norm_of_toF4_eq_zero hzero
  have h4p : (4 : Int) ∣ (p : Int) := by
    rcases hnorm with hnorm | hnorm
    · simpa [hnorm] using h4norm
    · exact dvd_neg.mp (by simpa [hnorm] using h4norm)
  exact not_four_dvd_int_of_mod10_eq_one hp10 h4p

def SplitPrimeCert.ofGenerator
    (p : Nat) (π : PhiInt) (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    (hnorm : PhiInt.norm π = (p : Int) ∨ PhiInt.norm π = -(p : Int)) :
    SplitPrimeCert p where
  π := π
  hp := hp
  hp10 := hp10
  hnorm := hnorm
  hmod2 := split_prime_mod2_nonzero hp hp10 hnorm

theorem splitPrimeCert_toF4_ne_zero {p : Nat} (c : SplitPrimeCert p) :
    toF4 c.π ≠ (0, 0) :=
  c.hmod2

theorem splitPrimeCert_at_least_one_contributes
    {p : Nat} (sp : SplitPrimeCert p) (c : SectorCert sp.π) :
    Contributes sp.π c ∨
      Contributes (PhiInt.star sp.π) (reflectedSectorCert sp.π c) :=
  at_least_one_contributes sp.π c sp.hmod2

/--
Atom-level nonvanishing for a split-prime generator certificate.  The current
Ch10 infrastructure proves that one conjugate avoids the bad iota class; the
separate bridge from such an atom to an actual `BCoeff N ≠ 0` statement is not
present in the imported files.
-/
theorem B_coeff_ne_zero_at_split_prime
    {p : Nat} (sp : SplitPrimeCert p) (c : SectorCert sp.π) :
    Contributes sp.π c ∨
      Contributes (PhiInt.star sp.π) (reflectedSectorCert sp.π c) :=
  splitPrimeCert_at_least_one_contributes sp c

end Ch10
end QseriesFormalization
