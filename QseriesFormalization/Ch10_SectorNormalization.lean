import QseriesFormalization.Ch10_UnitClassification
import QseriesFormalization.Ch10_ShintaniSector
import Mathlib.Tactic

/-!
# Ch10: Integral sector normalization

The archimedean fundamental-sector argument can be performed entirely in the
two integral coordinates `Tr` and `windowComp`.  For norm `-p`, their quadratic
identity forces an opposite-sign pair to lie beyond one of two rational
thresholds.  Multiplication by `eps` or `epsInv` then either enters the
same-sign window or strictly decreases the integral height.
-/

namespace QseriesFormalization
namespace Ch10

def sectorMeasure (x : PhiInt) : Nat :=
  (Tr x).natAbs + (windowComp x).natAbs

theorem trace_window_norm_identity (x : PhiInt) :
    Tr x ^ 2 + 3 * Tr x * windowComp x + windowComp x ^ 2 =
      -5 * PhiInt.norm x := by
  simp [Tr, windowComp, PhiInt.norm]
  ring

theorem sameWindowSign_neg_iff (x : PhiInt) :
    SameWindowSign (-x) ↔ SameWindowSign x := by
  simp only [SameWindowSign, Tr, windowComp, PhiInt.neg_a, PhiInt.neg_b]
  constructor <;> rintro (h | h)
  · right; omega
  · left; omega
  · right; omega
  · left; omega

theorem epsZPowMul_neg (m : Int) (x : PhiInt) :
    epsZPowMul m (-x) = -(epsZPowMul m x) := by
  simp only [epsZPowMul_eq_zpow_mul]
  ring

private theorem five_dvd_prime_of_trace_eq_zero
    {p : Nat} {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (htrace : Tr x = 0) : 5 ∣ p := by
  have hb : x.b = -2 * x.a := by
    simp only [Tr] at htrace
    omega
  have hpform : (p : Int) = 5 * x.a ^ 2 := by
    simp only [PhiInt.norm, hb] at hnorm
    nlinarith
  have hdiv : (5 : Int) ∣ (p : Int) := ⟨x.a ^ 2, hpform⟩
  exact_mod_cast hdiv

private theorem five_dvd_prime_of_windowComp_eq_zero
    {p : Nat} {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (hwindow : windowComp x = 0) : 5 ∣ p := by
  have hb : x.b = 3 * x.a := by
    simp only [windowComp] at hwindow
    omega
  have hpform : (p : Int) = 5 * x.a ^ 2 := by
    simp only [PhiInt.norm, hb] at hnorm
    nlinarith
  have hdiv : (5 : Int) ∣ (p : Int) := ⟨x.a ^ 2, hpform⟩
  exact_mod_cast hdiv

theorem trace_ne_zero_of_norm_eq_neg_split_prime
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int)) :
    Tr x ≠ 0 := by
  intro hzero
  have h5dvd := five_dvd_prime_of_trace_eq_zero hnorm hzero
  rcases (Nat.dvd_prime hp).mp h5dvd with h | h
  · omega
  · omega

theorem windowComp_ne_zero_of_norm_eq_neg_split_prime
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int)) :
    windowComp x ≠ 0 := by
  intro hzero
  have h5dvd := five_dvd_prime_of_windowComp_eq_zero hnorm hzero
  rcases (Nat.dvd_prime hp).mp h5dvd with h | h
  · omega
  · omega

private theorem sectorMeasure_neg (x : PhiInt) :
    sectorMeasure (-x) = sectorMeasure x := by
  have htrace : Tr (-x) = -Tr x := by
    simp [Tr]
    ring
  have hwindow : windowComp (-x) = -windowComp x := by
    simp [windowComp]
    ring
  rw [sectorMeasure, htrace, hwindow, Int.natAbs_neg, Int.natAbs_neg]
  rfl

private theorem exists_sameWindowSign_zpow_aux
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1) :
    ∀ n : Nat, ∀ x : PhiInt, sectorMeasure x = n →
      PhiInt.norm x = -(p : Int) →
      ∃ m : Int, SameWindowSign (epsZPowMul m x) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro x hmeasure hnorm
      let z : PhiInt := if 0 < Tr x then x else -x
      have hz_cases : z = x ∨ z = -x := by
        simp only [z]
        split <;> simp_all
      have htrace_x_ne := trace_ne_zero_of_norm_eq_neg_split_prime hp hp10 hnorm
      have hz_trace_pos : 0 < Tr z := by
        by_cases hpos : 0 < Tr x
        · have hz : z = x := by simp [z, hpos]
          rw [hz]
          exact hpos
        · have hneg : Tr x < 0 :=
            lt_of_le_of_ne (not_lt.mp hpos) htrace_x_ne
          have hz : z = -x := by simp [z, hpos]
          rw [hz]
          simp only [Tr, PhiInt.neg_a, PhiInt.neg_b]
          simp only [Tr] at hneg
          omega
      have hz_norm : PhiInt.norm z = -(p : Int) := by
        rcases hz_cases with hz | hz
        · simpa [hz] using hnorm
        · rw [hz, PhiInt.norm_neg, hnorm]
      have hz_measure : sectorMeasure z = n := by
        rcases hz_cases with hz | hz
        · simpa [hz] using hmeasure
        · rw [hz, sectorMeasure_neg, hmeasure]
      have hz_window_ne :=
        windowComp_ne_zero_of_norm_eq_neg_split_prime hp hp10 hz_norm
      have hz_result : ∃ m : Int, SameWindowSign (epsZPowMul m z) := by
        rcases lt_or_gt_of_ne hz_window_ne with hz_window_neg | hz_window_pos
        · have hquad := trace_window_norm_identity z
          rw [hz_norm] at hquad
          have hp_pos : 0 < (p : Int) := by exact_mod_cast hp.pos
          have hsplit :
              2 * (-windowComp z) < Tr z ∨
                2 * Tr z < -windowComp z := by
            by_contra hnot
            push Not at hnot
            have hprod :
                0 ≤ (2 * (-windowComp z) - Tr z) *
                  (2 * Tr z - (-windowComp z)) :=
              mul_nonneg (by omega) (by omega)
            nlinarith
          rcases hsplit with hwide_trace | hwide_window
          · let v := epsInvMul z
            have hv_norm : PhiInt.norm v = -(p : Int) := by
              simpa [v] using (norm_epsInvMul z).trans hz_norm
            by_cases hv_same : SameWindowSign v
            · refine ⟨-1, ?_⟩
              simpa [v, epsZPowMul, epsInvNatMul] using hv_same
            · have hv_trace_pos : 0 < Tr v := by
                rw [Tr_epsInvMul]
                omega
              have hv_window_ne :=
                windowComp_ne_zero_of_norm_eq_neg_split_prime hp hp10 hv_norm
              have hv_window_neg : windowComp v < 0 := by
                by_contra hnot
                have hv_window_pos : 0 < windowComp v :=
                  lt_of_le_of_ne (not_lt.mp hnot) hv_window_ne.symm
                exact hv_same (Or.inl ⟨hv_trace_pos, hv_window_pos⟩)
              have hv_measure_lt : sectorMeasure v < n := by
                have hv_cast : (sectorMeasure v : Int) = Tr v - windowComp v := by
                  simp [sectorMeasure, abs_of_pos hv_trace_pos,
                    abs_of_neg hv_window_neg]
                  ring
                have hz_cast : (sectorMeasure z : Int) = Tr z - windowComp z := by
                  simp [sectorMeasure, abs_of_pos hz_trace_pos,
                    abs_of_neg hz_window_neg]
                  ring
                have hcalc : (sectorMeasure v : Int) < sectorMeasure z := by
                  rw [hv_cast, hz_cast, Tr_epsInvMul, windowComp_epsInvMul]
                  omega
                rw [hz_measure] at hcalc
                exact_mod_cast hcalc
              rcases ih (sectorMeasure v) hv_measure_lt v rfl hv_norm with ⟨m, hm⟩
              refine ⟨m - 1, ?_⟩
              have hv_action : v = epsZPowMul (-1) z := by
                change v = epsInvMul (epsInvNatMul 0 z)
                simp [v, epsInvNatMul]
              have hcompose :
                  epsZPowMul (m - 1) z = epsZPowMul m v := by
                rw [sub_eq_add_neg, epsZPowMul_add, ← hv_action]
              rw [hcompose]
              exact hm
          · let v := epsMul z
            have hv_norm : PhiInt.norm v = -(p : Int) := by
              simpa [v] using (norm_epsMul z).trans hz_norm
            by_cases hv_same : SameWindowSign v
            · refine ⟨1, ?_⟩
              simpa [v, epsZPowMul, epsNatMul] using hv_same
            · have hv_window_neg : windowComp v < 0 := by
                rw [windowComp_epsMul]
                omega
              have hv_trace_ne :=
                trace_ne_zero_of_norm_eq_neg_split_prime hp hp10 hv_norm
              have hv_trace_pos : 0 < Tr v := by
                by_contra hnot
                have hv_trace_neg : Tr v < 0 :=
                  lt_of_le_of_ne (not_lt.mp hnot) hv_trace_ne
                exact hv_same (Or.inr ⟨hv_trace_neg, hv_window_neg⟩)
              have hv_measure_lt : sectorMeasure v < n := by
                have hv_cast : (sectorMeasure v : Int) = Tr v - windowComp v := by
                  simp [sectorMeasure, abs_of_pos hv_trace_pos,
                    abs_of_neg hv_window_neg]
                  ring
                have hz_cast : (sectorMeasure z : Int) = Tr z - windowComp z := by
                  simp [sectorMeasure, abs_of_pos hz_trace_pos,
                    abs_of_neg hz_window_neg]
                  ring
                have hcalc : (sectorMeasure v : Int) < sectorMeasure z := by
                  rw [hv_cast, hz_cast, Tr_epsMul, windowComp_epsMul]
                  omega
                rw [hz_measure] at hcalc
                exact_mod_cast hcalc
              rcases ih (sectorMeasure v) hv_measure_lt v rfl hv_norm with ⟨m, hm⟩
              refine ⟨m + 1, ?_⟩
              have hv_action : v = epsZPowMul 1 z := by
                simp [v, epsZPowMul, epsNatMul]
              have hcompose :
                  epsZPowMul (m + 1) z = epsZPowMul m v := by
                rw [epsZPowMul_add, ← hv_action]
              rw [hcompose]
              exact hm
        · refine ⟨0, ?_⟩
          simpa [epsZPowMul, epsNatMul, SameWindowSign] using
            (Or.inl ⟨hz_trace_pos, hz_window_pos⟩)
      rcases hz_result with ⟨m, hm⟩
      rcases hz_cases with hz | hz
      · exact ⟨m, by simpa [hz] using hm⟩
      · refine ⟨m, ?_⟩
        rw [hz, epsZPowMul_neg, sameWindowSign_neg_iff] at hm
        exact hm

/-- Every norm `-p` element at a split rational prime has a signed
fundamental-window associate. -/
theorem exists_sameWindowSign_zpow
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int)) :
    ∃ m : Int, SameWindowSign (epsZPowMul m x) :=
  exists_sameWindowSign_zpow_aux hp hp10 (sectorMeasure x) x rfl hnorm

/-- A sector certificate carrying the actual integral normalization, rather
than only an unconstrained residue label. -/
structure GeometricSectorCert (x : PhiInt) where
  lift : Int
  normalized : SameWindowSign (epsZPowMul (-lift) x)

/-- The integral lift is determined uniquely by the strict signed fundamental
window.  This turns `GeometricSectorCert` into data with proof-irrelevant
choice, rather than a relabelled arbitrary `SectorCert`. -/
theorem GeometricSectorCert.lift_unique {x : PhiInt}
    (c d : GeometricSectorCert x) : c.lift = d.lift := by
  by_contra hne
  have hdiff : c.lift - d.lift ≠ 0 := sub_ne_zero.mpr hne
  have hop := epsZPowMul_opposite_of_ne_zero hdiff c.normalized
  have heq :
      epsZPowMul (c.lift - d.lift) (epsZPowMul (-c.lift) x) =
        epsZPowMul (-d.lift) x := by
    rw [← epsZPowMul_add]
    congr 1
    ring
  rw [heq] at hop
  exact sameWindowSign_not_opposite d.normalized hop

def GeometricSectorCert.toSectorCert {x : PhiInt}
    (c : GeometricSectorCert x) : SectorCert x :=
  ⟨(c.lift : ZMod 3)⟩

theorem exists_geometricSectorCert
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int)) :
    Nonempty (GeometricSectorCert x) := by
  rcases exists_sameWindowSign_zpow hp hp10 hnorm with ⟨m, hm⟩
  exact ⟨⟨-m, by simpa using hm⟩⟩

end Ch10
end QseriesFormalization
