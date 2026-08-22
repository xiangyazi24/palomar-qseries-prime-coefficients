import QseriesFormalization.Ch10_ConeRecognition
import QseriesFormalization.Ch10_NormTheta_Algebra

/-!
# Ch10: One atom in the cone window

Integer powers of the fundamental unit are represented by iteration of its two
coordinate matrices.  The proof tracks the trace/window-coordinate pair.  A
nonzero unit power sends a same-sign pair to an opposite-sign pair, so it cannot
carry one cone atom to another.
-/

namespace QseriesFormalization
namespace Ch10

/-- Multiplication by `eps^{-1} = 2 - phi`. -/
def epsInvMul (x : PhiInt) : PhiInt :=
  ⟨2 * x.a - x.b, -x.a + x.b⟩

def epsNatMul : Nat → PhiInt → PhiInt
  | 0, x => x
  | n + 1, x => epsMul (epsNatMul n x)

def epsInvNatMul : Nat → PhiInt → PhiInt
  | 0, x => x
  | n + 1, x => epsInvMul (epsInvNatMul n x)

/-- The action of the integral power `eps^m` on `PhiInt`. -/
def epsZPowMul : Int → PhiInt → PhiInt
  | Int.ofNat n, x => epsNatMul n x
  | Int.negSucc n, x => epsInvNatMul (n + 1) x

/-- Associate relation under the norm-one unit group `{+-eps^m}`. -/
def sameIdeal (x y : PhiInt) : Prop :=
  ∃ (m : Int) (negative : Bool),
    y = match negative with
      | false => epsZPowMul m x
      | true => -(epsZPowMul m x)

def SameWindowSign (x : PhiInt) : Prop :=
  (0 < Tr x ∧ 0 < windowComp x) ∨
  (Tr x < 0 ∧ windowComp x < 0)

def OppositeWindowSign (x : PhiInt) : Prop :=
  (0 < Tr x ∧ windowComp x < 0) ∨
  (Tr x < 0 ∧ 0 < windowComp x)

private def ForwardMixed (x : PhiInt) : Prop :=
  (0 < Tr x ∧ windowComp x < 0 ∧ 0 < Tr x + windowComp x) ∨
  (Tr x < 0 ∧ 0 < windowComp x ∧ Tr x + windowComp x < 0)

private def BackwardMixed (x : PhiInt) : Prop :=
  (Tr x < 0 ∧ 0 < windowComp x ∧ 0 < Tr x + windowComp x) ∨
  (0 < Tr x ∧ windowComp x < 0 ∧ Tr x + windowComp x < 0)

theorem Tr_epsMul (x : PhiInt) :
    Tr (epsMul x) = 3 * Tr x + windowComp x := by
  simp [Tr, windowComp, epsMul]
  ring

theorem windowComp_epsMul (x : PhiInt) :
    windowComp (epsMul x) = -Tr x := by
  simp [Tr, windowComp, epsMul]
  ring

theorem Tr_epsInvMul (x : PhiInt) :
    Tr (epsInvMul x) = -windowComp x := by
  simp [Tr, windowComp, epsInvMul]
  ring

theorem windowComp_epsInvMul (x : PhiInt) :
    windowComp (epsInvMul x) = Tr x + 3 * windowComp x := by
  simp [Tr, windowComp, epsInvMul]
  ring

private theorem forwardMixed_epsMul {x : PhiInt} (h : ForwardMixed x) :
    ForwardMixed (epsMul x) := by
  simp only [ForwardMixed] at h ⊢
  rw [Tr_epsMul, windowComp_epsMul]
  rcases h with h | h
  · left
    omega
  · right
    omega

private theorem backwardMixed_epsInvMul {x : PhiInt} (h : BackwardMixed x) :
    BackwardMixed (epsInvMul x) := by
  simp only [BackwardMixed] at h ⊢
  rw [Tr_epsInvMul, windowComp_epsInvMul]
  rcases h with h | h
  · left
    omega
  · right
    omega

private theorem first_forward_mixed {x : PhiInt} (h : SameWindowSign x) :
    ForwardMixed (epsMul x) := by
  simp only [SameWindowSign] at h
  simp only [ForwardMixed]
  rw [Tr_epsMul, windowComp_epsMul]
  rcases h with h | h
  · left
    omega
  · right
    omega

private theorem first_backward_mixed {x : PhiInt} (h : SameWindowSign x) :
    BackwardMixed (epsInvMul x) := by
  simp only [SameWindowSign] at h
  simp only [BackwardMixed]
  rw [Tr_epsInvMul, windowComp_epsInvMul]
  rcases h with h | h
  · left
    omega
  · right
    omega

private theorem epsNatMul_succ_mixed (n : Nat) {x : PhiInt}
    (h : SameWindowSign x) : ForwardMixed (epsNatMul (n + 1) x) := by
  induction n with
  | zero => simpa [epsNatMul] using first_forward_mixed h
  | succ n ih =>
      simpa [epsNatMul] using forwardMixed_epsMul ih

private theorem epsInvNatMul_succ_mixed (n : Nat) {x : PhiInt}
    (h : SameWindowSign x) : BackwardMixed (epsInvNatMul (n + 1) x) := by
  induction n with
  | zero => simpa [epsInvNatMul] using first_backward_mixed h
  | succ n ih =>
      simpa [epsInvNatMul] using backwardMixed_epsInvMul ih

private theorem forwardMixed_opposite {x : PhiInt} (h : ForwardMixed x) :
    OppositeWindowSign x := by
  simp only [ForwardMixed] at h
  simp only [OppositeWindowSign]
  rcases h with h | h
  · exact Or.inl ⟨h.1, h.2.1⟩
  · exact Or.inr ⟨h.1, h.2.1⟩

private theorem backwardMixed_opposite {x : PhiInt} (h : BackwardMixed x) :
    OppositeWindowSign x := by
  simp only [BackwardMixed] at h
  simp only [OppositeWindowSign]
  rcases h with h | h
  · exact Or.inr ⟨h.1, h.2.1⟩
  · exact Or.inl ⟨h.1, h.2.1⟩

theorem epsZPowMul_opposite_of_ne_zero {m : Int} {x : PhiInt}
    (hm : m ≠ 0) (hx : SameWindowSign x) :
    OppositeWindowSign (epsZPowMul m x) := by
  cases m with
  | ofNat n =>
      cases n with
      | zero => exact (hm rfl).elim
      | succ n =>
          exact forwardMixed_opposite (epsNatMul_succ_mixed n hx)
  | negSucc n =>
      exact backwardMixed_opposite (epsInvNatMul_succ_mixed n hx)

theorem oppositeWindowSign_neg {x : PhiInt} (h : OppositeWindowSign x) :
    OppositeWindowSign (-x) := by
  simp only [OppositeWindowSign] at h ⊢
  rcases h with h | h
  · right
    simp only [Tr, windowComp, PhiInt.neg_a, PhiInt.neg_b]
    simp only [Tr, windowComp] at h
    omega
  · left
    simp only [Tr, windowComp, PhiInt.neg_a, PhiInt.neg_b]
    simp only [Tr, windowComp] at h
    omega

theorem sameWindowSign_not_opposite {x : PhiInt} :
    SameWindowSign x → ¬ OppositeWindowSign x := by
  intro hs ho
  simp only [SameWindowSign] at hs
  simp only [OppositeWindowSign] at ho
  rcases hs with hs | hs <;> rcases ho with ho | ho <;> omega

theorem sameWindowSign_beta_of_inCones {k r : Int} (h : InCones k r) :
    SameWindowSign (beta k r) := by
  rw [inCones_iff_coordinate_signs] at h
  simp only [SameWindowSign]
  rcases h with h | h
  · left; omega
  · right; omega

theorem neg_not_in_L (x : PhiInt) (hx : InL x) : ¬ InL (-x) := by
  simp only [InL, PhiInt.neg_a, PhiInt.neg_b] at hx ⊢
  rcases hx with ⟨m, hm⟩
  rintro ⟨n, hn⟩
  omega

private theorem beta_injective {k r k' r' : Int}
    (h : beta k r = beta k' r') : k = k' ∧ r = r' := by
  have ha := congrArg PhiInt.a h
  have hb := congrArg PhiInt.b h
  simp only [beta, PhiInt.mk_a, PhiInt.mk_b] at ha hb
  omega

/-- One cone point in a fixed associate class. -/
theorem one_atom : ∀ (k r k' r' : Int),
    InCones k r → InCones k' r' →
    sameIdeal (beta k r) (beta k' r') →
    PhiInt.norm (beta k r) = PhiInt.norm (beta k' r') →
    k = k' ∧ r = r' := by
  intro k r k' r' hk hk' hassoc _hnorm
  have hsign := sameWindowSign_beta_of_inCones hk
  have hsign' := sameWindowSign_beta_of_inCones hk'
  rcases hassoc with ⟨m, negative, hrel⟩
  by_cases hm : m = 0
  · subst m
    cases negative with
    | false =>
        change beta k' r' = epsZPowMul 0 (beta k r) at hrel
        simp [epsZPowMul, epsNatMul] at hrel
        exact beta_injective hrel.symm
    | true =>
        change beta k' r' = -(epsZPowMul 0 (beta k r)) at hrel
        simp [epsZPowMul, epsNatMul] at hrel
        have hL' : InL (-(beta k r)) := by
          rw [← hrel]
          exact beta_mem_L k' r'
        exact (neg_not_in_L (beta k r) (beta_mem_L k r) hL').elim
  · have hop := epsZPowMul_opposite_of_ne_zero hm hsign
    cases negative with
    | false =>
        change beta k' r' = epsZPowMul m (beta k r) at hrel
        rw [hrel] at hsign'
        exact (sameWindowSign_not_opposite hsign' hop).elim
    | true =>
        change beta k' r' = -(epsZPowMul m (beta k r)) at hrel
        have hneg := oppositeWindowSign_neg hop
        rw [hrel] at hsign'
        exact (sameWindowSign_not_opposite hsign' hneg).elim

end Ch10
end QseriesFormalization
