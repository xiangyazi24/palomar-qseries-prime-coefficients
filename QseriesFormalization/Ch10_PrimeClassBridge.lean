import QseriesFormalization.Ch10_PrimeFiniteAtoms
import Mathlib.Tactic

/-!
# Ch10: Bidirectional bridge between prime classes and finite atoms

A good geometric class produces a finite coefficient atom.  Conversely, a
finite atom in a class is already the uniquely normalized, mod-five-oriented
representative of that class, so the class must contribute.  This converse is
the semantic input needed for exact counting rather than a mere upper bound.
-/

namespace QseriesFormalization
namespace Ch10

theorem primeLevel_spec {p : Nat} (hp10 : p % 10 = 1) :
    10 * ((p - 1) / 10) + 1 = p := by
  omega

/-- Any same-sign associate of `x` is one of the two overall signs of the
geometrically normalized representative. -/
theorem eq_normalized_or_neg_of_sameIdeal_sameWindowSign
    {x y : PhiInt} (c : GeometricSectorCert x)
    (hy : SameWindowSign y) (hxy : sameIdeal x y) :
    y = epsZPowMul (-c.lift) x ∨
      y = -(epsZPowMul (-c.lift) x) := by
  rcases hxy with ⟨m, negative, hrel⟩
  by_cases hm : m = -c.lift
  · cases negative with
    | false => exact Or.inl (by simpa [hm] using hrel)
    | true => exact Or.inr (by simpa [hm] using hrel)
  · have hnonzero : m + c.lift ≠ 0 := by omega
    have hop := epsZPowMul_opposite_of_ne_zero hnonzero c.normalized
    have heq :
        epsZPowMul (m + c.lift) (epsZPowMul (-c.lift) x) =
          epsZPowMul m x := by
      calc
        epsZPowMul (m + c.lift) (epsZPowMul (-c.lift) x) =
            epsZPowMul ((m + c.lift) + (-c.lift)) x := by
              exact (epsZPowMul_add (m + c.lift) (-c.lift) x).symm
        _ = epsZPowMul m x := by congr 1; ring
    rw [heq] at hop
    cases negative with
    | false =>
        have hopy : OppositeWindowSign y := by
          change y = epsZPowMul m x at hrel
          rw [hrel]
          exact hop
        exact (sameWindowSign_not_opposite hy hopy).elim
    | true =>
        have hneg := oppositeWindowSign_neg hop
        have hopy : OppositeWindowSign y := by
          change y = -(epsZPowMul m x) at hrel
          rw [hrel]
          exact hneg
        exact (sameWindowSign_not_opposite hy hopy).elim

theorem windowComp_zmod5_eq_one_of_mem_L {y : PhiInt} (hL : InL y) :
    ((windowComp y : Int) : ZMod 5) = 1 := by
  rcases hL with ⟨n, hn⟩
  have hcoord : windowComp y - 1 = 10 * n := by
    simpa [windowComp] using hn
  have hzero : (((windowComp y - 1 : Int) : ZMod 5)) = 0 := by
    rw [hcoord]
    push_cast
    rw [show (10 : ZMod 5) = 0 by decide, zero_mul]
  push_cast at hzero
  exact sub_eq_zero.mp hzero

/-- A same-sign finite-lattice associate forces the corresponding geometric
class to contribute. -/
theorem contributes_of_sameIdeal_mem_L_sameWindowSign
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (c : GeometricSectorCert x)
    (o : OrientedSectorNormalization (p := p) x c)
    {y : PhiInt} (hy : SameWindowSign y) (hL : InL y)
    (hxy : sameIdeal x y) :
    Contributes x c.toSectorCert := by
  let oy : OrientedSectorNormalization (p := p) x c := {
    oriented := y
    eq_normalized_or_neg :=
      eq_normalized_or_neg_of_sameIdeal_sameWindowSign c hy hxy
    window_mod5 := windowComp_zmod5_eq_one_of_mem_L hL
  }
  have heq : o.oriented = y := o.oriented_unique oy
  apply (contributes_iff_oriented_mem_L hp hp10 hnorm o).2
  simpa [heq] using hL

theorem eq_oriented_of_sameIdeal_mem_L_sameWindowSign
    {p : Nat} {x : PhiInt} (c : GeometricSectorCert x)
    (o : OrientedSectorNormalization (p := p) x c)
    {y : PhiInt} (hy : SameWindowSign y) (hL : InL y)
    (hxy : sameIdeal x y) : y = o.oriented := by
  let oy : OrientedSectorNormalization (p := p) x c := {
    oriented := y
    eq_normalized_or_neg :=
      eq_normalized_or_neg_of_sameIdeal_sameWindowSign c hy hxy
    window_mod5 := windowComp_zmod5_eq_one_of_mem_L hL
  }
  exact (o.oriented_unique oy).symm

/-- A finite atom together with its associate-class assignment. -/
structure PrimeClassAtom (base : PhiInt) (N : Nat) where
  atom : PrimeFinAtom N
  same : sameIdeal base atom.beta

theorem PrimeClassAtom.atom_eq {base : PhiInt} {N : Nat}
    (u v : PrimeClassAtom base N) : u.atom = v.atom := by
  apply PrimeFinAtom.kr_injective
  have hs : sameIdeal u.atom.beta v.atom.beta :=
    sameIdeal_trans (sameIdeal_symm u.same) v.same
  have hu := PrimeFinAtom.spec u.atom
  have hv := PrimeFinAtom.spec v.atom
  have hcoords := one_atom u.atom.kr.1 u.atom.kr.2
    v.atom.kr.1 v.atom.kr.2 hu.1 hv.1 hs (by
      calc
        PhiInt.norm (beta u.atom.kr.1 u.atom.kr.2) =
            -(10 * (N : Int) + 1) := by
              simpa only [PrimeFinAtom.beta] using
                PrimeFinAtom.norm u.atom
        _ = PhiInt.norm (beta v.atom.kr.1 v.atom.kr.2) := by
              symm
              simpa only [PrimeFinAtom.beta] using
                PrimeFinAtom.norm v.atom)
  exact Prod.ext hcoords.1 hcoords.2

/-- Forward half of the class bridge, returning an actual finite atom rather
than only positivity of the total count. -/
theorem exists_primeClassAtom_of_contributes
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (c : GeometricSectorCert x)
    (o : OrientedSectorNormalization (p := p) x c)
    (hcontrib : Contributes x c.toSectorCert) :
    Nonempty (PrimeClassAtom x ((p - 1) / 10)) := by
  rcases exists_prime_cone_atom_of_contributes hp hp10 hnorm o hcontrib with
    ⟨k, r, hbeta, hcones, hE⟩
  let a := PrimeFinAtom.packConeAtom k r hcones (by exact_mod_cast hE)
  have hkr : a.kr = (k, r) := by
    exact PrimeFinAtom.kr_packConeAtom k r hcones (by exact_mod_cast hE)
  have habeta : a.beta = o.oriented := by
    simp only [PrimeFinAtom.beta]
    rw [hkr]
    exact hbeta
  have hsame : sameIdeal x a.beta := by
    rw [habeta]
    rcases o.eq_normalized_or_neg with h | h
    · exact ⟨-c.lift, false, h⟩
    · exact ⟨-c.lift, true, h⟩
  exact ⟨⟨a, hsame⟩⟩

/-- Converse half of the class bridge. -/
theorem contributes_of_primeClassAtom
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (c : GeometricSectorCert x)
    (o : OrientedSectorNormalization (p := p) x c)
    (a : PrimeClassAtom x ((p - 1) / 10)) :
    Contributes x c.toSectorCert := by
  exact contributes_of_sameIdeal_mem_L_sameWindowSign hp hp10 hnorm c o
    a.atom.sameWindowSign a.atom.mem_L a.same

theorem contributes_iff_primeClassAtom
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (c : GeometricSectorCert x)
    (o : OrientedSectorNormalization (p := p) x c) :
    Contributes x c.toSectorCert ↔
      Nonempty (PrimeClassAtom x ((p - 1) / 10)) := by
  constructor
  · exact exists_primeClassAtom_of_contributes hp hp10 hnorm c o
  · rintro ⟨a⟩
    exact contributes_of_primeClassAtom hp hp10 hnorm c o a

theorem PrimeFinAtom.class_cover
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (a : PrimeFinAtom ((p - 1) / 10)) :
    sameIdeal x a.beta ∨ sameIdeal (PhiInt.star x) a.beta := by
  rcases five_isSquare_zmod_of_prime_mod10_one hp hp10 with ⟨t, ht⟩
  apply norm_prime_two_sameIdeal_classes hp hp10
    (by simpa [pow_two] using ht) hnorm
  rw [PrimeFinAtom.norm]
  have hlevel :
      ((10 * ((p - 1) / 10) + 1 : Nat) : Int) = (p : Int) := by
    exact_mod_cast primeLevel_spec hp10
  push_cast at hlevel
  exact congrArg Neg.neg hlevel

theorem geometric_at_least_one_contributes
    {p : Nat} (hp : Nat.Prime p) (hp10 : p % 10 = 1)
    {x : PhiInt} (hnorm : PhiInt.norm x = -(p : Int))
    (c : GeometricSectorCert x) :
    Contributes x c.toSectorCert ∨
      Contributes (PhiInt.star x) c.reflected.toSectorCert := by
  have hx : toF4 x ≠ (0, 0) :=
    split_prime_mod2_nonzero hp hp10 (Or.inr hnorm)
  have h := at_least_one_contributes x c.toSectorCert hx
  rw [← c.toSectorCert_reflected] at h
  exact h

end Ch10
end QseriesFormalization
