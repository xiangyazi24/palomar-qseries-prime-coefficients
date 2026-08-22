import QseriesFormalization.Ch10_OneAtom
import QseriesFormalization.Ch10_F4

/-!
# Ch10: Conjugate atoms and sign coherence

For an atom whose second parameter is even, conjugation followed by `-eps`
swaps the two half-parameters.  The swap preserves each cone and makes both
parity signs equal to `+1`.
-/

namespace QseriesFormalization
namespace Ch10

def conjAtom (p : Int × Int) : Int × Int := (p.2 / 2, 2 * p.1)

theorem conj_atom_identity (k t : Int) :
    -(PhiInt.eps * PhiInt.star (beta k (2 * t))) = beta t (2 * k) := by
  ext <;> simp [PhiInt.eps, PhiInt.star, beta] <;> ring

theorem conjAtom_even_formula (k t : Int) :
    conjAtom (k, 2 * t) = (t, 2 * k) := by
  apply Prod.ext
  · change (2 * t) / 2 = t
    exact Int.mul_ediv_cancel_left t (by norm_num)
  · rfl

theorem conjAtom_even_involution (k t : Int) :
    conjAtom (conjAtom (k, 2 * t)) = (k, 2 * t) := by
  calc
    conjAtom (conjAtom (k, 2 * t)) = conjAtom (t, 2 * k) := by
      rw [conjAtom_even_formula]
    _ = (k, 2 * t) := conjAtom_even_formula t k

theorem conjAtom_ACone_iff (k t : Int) :
    InACone k (2 * t) ↔ InACone t (2 * k) := by
  simp only [InACone]
  omega

theorem conjAtom_DCone_iff (k t : Int) :
    InDCone k (2 * t) ↔ InDCone t (2 * k) := by
  simp only [InDCone]
  omega

theorem conjAtom_cones_iff (k t : Int) :
    InCones k (2 * t) ↔ InCones t (2 * k) := by
  simp only [InCones, conjAtom_ACone_iff, conjAtom_DCone_iff]

theorem conjAtom_even_coordinates (k t : Int) :
    Even (2 * t) ∧ Even (2 * k) := by
  constructor
  · exact ⟨t, by ring⟩
  · exact ⟨k, by ring⟩

theorem negOnePowInt_two_mul (n : Int) : negOnePowInt (2 * n) = 1 := by
  apply negOnePowInt_even
  omega

/-- The explicit conjugate pair has the same full `BWeight`. -/
theorem conjAtom_weight_eq (k t : Int) (h : InCones k (2 * t)) :
    BWeight k (2 * t) = BWeight t (2 * k) := by
  rcases h with hA | hD
  · have hA' := (conjAtom_ACone_iff k t).mp hA
    have hD : ¬ InDCone k (2 * t) := by
      intro hbad
      rcases hA with ⟨hk, ht⟩
      rcases hbad with ⟨hk', ht'⟩
      omega
    have hD' : ¬ InDCone t (2 * k) := by
      intro hbad
      rcases hA' with ⟨ht, hk⟩
      rcases hbad with ⟨ht', hk'⟩
      omega
    simp [BWeight, hA, hA', hD, hD', negOnePowInt_two_mul]
  · have hD' := (conjAtom_DCone_iff k t).mp hD
    have hA : ¬ InACone k (2 * t) := by
      intro hbad
      rcases hD with ⟨hk, ht⟩
      rcases hbad with ⟨hk', ht'⟩
      omega
    have hA' : ¬ InACone t (2 * k) := by
      intro hbad
      rcases hD' with ⟨ht, hk⟩
      rcases hbad with ⟨ht', hk'⟩
      omega
    simp [BWeight, hA, hA', hD, hD', negOnePowInt_two_mul]

/-- The residue class of `phi` in the chosen `F_4` coordinates. -/
def phiF4 : ZMod 2 × ZMod 2 := (0, 1)

/-- If `beta k r` is congruent to `phi` modulo two, then `r` is even. -/
theorem beta_even_r_of_toF4_eq_phiF4 (k r : Int)
    (h : toF4 (beta k r) = phiF4) : Even r := by
  have haZ : ((r - 2 * k : Int) : ZMod 2) = 0 := by
    have ha := congrArg Prod.fst h
    simpa [toF4, beta, phiF4] using ha
  rcases (ZMod.intCast_zmod_eq_zero_iff_dvd (r - 2 * k) 2).mp haZ with
    ⟨n, hn⟩
  exact ⟨k + n, by omega⟩

end Ch10
end QseriesFormalization
