import QseriesFormalization.Ch10_PrimeExactCount
import Mathlib.Tactic

/-!
# Ch10: Prime-atom sign coherence

When both conjugate prime classes contribute, the left iota value is one.
The normalized left atom is therefore congruent to `phi` modulo two, so its
second cone coordinate is even.  Conjugation followed by `-eps` then gives the
right atom by the explicit coordinate swap `(k, 2t) -> (t, 2k)`.  The existing
full `BWeight` identity for this swap proves equality of the two signs.
-/

namespace QseriesFormalization
namespace Ch10

theorem toF4_eq_phiF4_of_ne_zero_discreteLog_eq_two
    (z : ZMod 2 × ZMod 2) (hz : z ≠ (0, 0))
    (hlog : discreteLog z = 2) : z = phiF4 := by
  revert hz hlog
  rcases z with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> decide

theorem both_good_atom_coordinates
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (c : GeometricSectorCert x)
    (o : OrientedSectorNormalization (p := p) x c)
    (hleft : Contributes x c.toSectorCert)
    (hright : Contributes (PhiInt.star x) c.reflected.toSectorCert)
    (left : PrimeClassAtom x ((p - 1) / 10))
    (right : PrimeClassAtom (PhiInt.star x) ((p - 1) / 10)) :
    ∃ k t : Int,
      left.atom.kr = (k, 2 * t) ∧
        right.atom.kr = (t, 2 * k) := by
  have hiota : iotaCert x c.toSectorCert = 1 :=
    (both_contribute_iff_iota_eq_one hp hp10 hnorm c).1 ⟨hleft, hright⟩
  have hleft_oriented : left.atom.beta = o.oriented :=
    eq_oriented_of_sameIdeal_mem_L_sameWindowSign c o
      left.atom.sameWindowSign left.atom.mem_L left.same
  have horient_norm := o.norm_eq_neg_prime hnorm
  have horient_nonzero : toF4 o.oriented ≠ (0, 0) :=
    split_prime_mod2_nonzero hp hp10 (Or.inr horient_norm)
  have hlambda := o.lambda_eq_neg_iota hp hp10 hnorm
  have hlambda_two : lambdaOf o.oriented = 2 := by
    rw [hlambda, hiota]
    decide
  have horient_f4 : toF4 o.oriented = phiF4 :=
    toF4_eq_phiF4_of_ne_zero_discreteLog_eq_two
      (toF4 o.oriented) horient_nonzero hlambda_two
  rcases hkr : left.atom.kr with ⟨k, r⟩
  have hleft_beta : left.atom.beta = beta k r := by
    simp only [PrimeFinAtom.beta]
    rw [hkr]
  have hbeta_f4 : toF4 (beta k r) = phiF4 := by
    rw [← hleft_beta, hleft_oriented]
    exact horient_f4
  have heven : Even r := beta_even_r_of_toF4_eq_phiF4 k r hbeta_f4
  rcases heven with ⟨t, ht⟩
  have hrt : r = 2 * t := by omega
  have hleft_kr : left.atom.kr = (k, 2 * t) := by
    rw [hkr, hrt]
  have hleft_cone : InCones k (2 * t) := by
    have h := (PrimeFinAtom.spec left.atom).1
    rw [hleft_kr] at h
    exact h
  have hleft_E : E k (2 * t) = (((p - 1) / 10 : Nat) : Int) := by
    have h := (PrimeFinAtom.spec left.atom).2
    rw [hleft_kr] at h
    exact h
  have hstar_class :
      sameIdeal (PhiInt.star x) (PhiInt.star (beta k (2 * t))) := by
    have h := sameIdeal_star left.same
    rw [hleft_beta, hrt] at h
    exact h
  have hswap_class :
      sameIdeal (PhiInt.star (beta k (2 * t))) (beta t (2 * k)) := by
    refine ⟨1, true, ?_⟩
    change beta t (2 * k) =
      -(epsZPowMul 1 (PhiInt.star (beta k (2 * t))))
    simp only [epsZPowMul, epsNatMul]
    rw [epsMul_eq_mul]
    exact (conj_atom_identity k t).symm
  have hcandidate_class :
      sameIdeal (PhiInt.star x) (beta t (2 * k)) :=
    sameIdeal_trans hstar_class hswap_class
  have hcandidate_cone : InCones t (2 * k) :=
    (conjAtom_cones_iff k t).mp hleft_cone
  have hnorm_swap :
      PhiInt.norm (beta t (2 * k)) = PhiInt.norm (beta k (2 * t)) := by
    rw [← conj_atom_identity k t, PhiInt.norm_neg, PhiInt.norm_mul,
      PhiInt.norm_eps, PhiInt.norm_star]
    ring
  have hcandidate_E :
      E t (2 * k) = (((p - 1) / 10 : Nat) : Int) := by
    have hleft_norm_formula := norm_beta k (2 * t)
    have hright_norm_formula := norm_beta t (2 * k)
    omega
  let candidate := PrimeFinAtom.packConeAtom t (2 * k)
    hcandidate_cone hcandidate_E
  have hcandidate_kr : candidate.kr = (t, 2 * k) := by
    exact PrimeFinAtom.kr_packConeAtom t (2 * k)
      hcandidate_cone hcandidate_E
  have hcandidate_beta : candidate.beta = beta t (2 * k) := by
    simp only [PrimeFinAtom.beta]
    rw [hcandidate_kr]
  let candidateClass :
      PrimeClassAtom (PhiInt.star x) ((p - 1) / 10) := {
    atom := candidate
    same := by
      rw [hcandidate_beta]
      exact hcandidate_class
  }
  have hright_atom : right.atom = candidate :=
    right.atom_eq candidateClass
  refine ⟨k, t, by simpa only [hkr] using hleft_kr, ?_⟩
  rw [hright_atom]
  exact hcandidate_kr

theorem both_good_atom_weights_eq
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (c : GeometricSectorCert x)
    (o : OrientedSectorNormalization (p := p) x c)
    (hleft : Contributes x c.toSectorCert)
    (hright : Contributes (PhiInt.star x) c.reflected.toSectorCert)
    (left : PrimeClassAtom x ((p - 1) / 10))
    (right : PrimeClassAtom (PhiInt.star x) ((p - 1) / 10)) :
    left.atom.weight = right.atom.weight := by
  rcases both_good_atom_coordinates hp hp10 hnorm c o hleft hright
      left right with ⟨k, t, hleft_kr, hright_kr⟩
  rw [PrimeFinAtom.weight_eq_BWeight, PrimeFinAtom.weight_eq_BWeight,
    hleft_kr, hright_kr]
  exact conjAtom_weight_eq k t (by
    have h := (PrimeFinAtom.spec left.atom).1
    rw [hleft_kr] at h
    exact h)

end Ch10
end QseriesFormalization
