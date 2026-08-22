import QseriesFormalization.Ch10_GeometricReflection
import QseriesFormalization.Ch10_PrimeBridge
import Mathlib.Tactic

/-!
# Ch10: A unified finite type of coefficient atoms

The two finite boxes defining `ACoeff` and `DCoeff` are combined into one
finite type.  Its decoding to integral cone coordinates is injective, and the
four completeness bounds give an exact packing operation for every integral
cone atom at the requested level.
-/

namespace QseriesFormalization
namespace Ch10

abbrev PrimeFinAtom (N : Nat) :=
  (↑(AAtoms N)) ⊕ (↑(DAtoms N))

namespace PrimeFinAtom

def kr {N : Nat} : PrimeFinAtom N → Int × Int
  | .inl q => ((q.1.1 : Int), (q.1.2 : Int))
  | .inr q => (-((q.1.1 : Int) + 1), -((q.1.2 : Int) + 1))

def beta {N : Nat} (a : PrimeFinAtom N) : PhiInt :=
  Ch10.beta a.kr.1 a.kr.2

def weight {N : Nat} : PrimeFinAtom N → Int
  | .inl q => AAtomWeight q.1
  | .inr q => DAtomWeight q.1

@[simp] theorem card_eq_atomCount (N : Nat) :
    Fintype.card (PrimeFinAtom N) = atomCount N := by
  simp [PrimeFinAtom, atomCount]

theorem spec {N : Nat} (a : PrimeFinAtom N) :
    InCones a.kr.1 a.kr.2 ∧ E a.kr.1 a.kr.2 = (N : Int) := by
  cases a with
  | inl q =>
      rcases Finset.mem_filter.mp q.2 with ⟨hbox, hE⟩
      rcases Finset.mem_product.mp hbox with ⟨hk, hr⟩
      simp only [Finset.mem_range] at hk hr
      exact ⟨Or.inl ⟨by simp [kr], by simp [kr]⟩, by simpa [kr] using hE⟩
  | inr q =>
      rcases Finset.mem_filter.mp q.2 with ⟨hbox, hE⟩
      rcases Finset.mem_product.mp hbox with ⟨hk, hr⟩
      simp only [Finset.mem_range] at hk hr
      exact ⟨Or.inr ⟨by
        change -((q.1.1 : Int) + 1) < 0
        omega, by
        change -((q.1.2 : Int) + 1) < 0
        omega⟩, by simpa [kr] using hE⟩

theorem norm {N : Nat} (a : PrimeFinAtom N) :
    PhiInt.norm a.beta = -(10 * (N : Int) + 1) := by
  have hn := norm_beta a.kr.1 a.kr.2
  have hE := (spec a).2
  simp only [PrimeFinAtom.beta]
  omega

theorem mem_L {N : Nat} (a : PrimeFinAtom N) : InL a.beta := by
  exact beta_mem_L _ _

theorem sameWindowSign {N : Nat} (a : PrimeFinAtom N) :
    SameWindowSign a.beta := by
  exact sameWindowSign_beta_of_inCones (spec a).1

theorem weight_eq_BWeight {N : Nat} (a : PrimeFinAtom N) :
    a.weight = BWeight a.kr.1 a.kr.2 := by
  cases a with
  | inl q =>
      have hA : InACone (q.1.1 : Int) (q.1.2 : Int) := by
        exact ⟨by positivity, by positivity⟩
      change AAtomWeight q.1 =
        BWeight (q.1.1 : Int) (q.1.2 : Int)
      rw [BWeight]
      simp only [if_pos hA]
      rfl
  | inr q =>
      have hD : InDCone (-((q.1.1 : Int) + 1))
          (-((q.1.2 : Int) + 1)) := by
        exact ⟨by omega, by omega⟩
      have hnA : ¬ InACone (-((q.1.1 : Int) + 1))
          (-((q.1.2 : Int) + 1)) := by
        intro hbad
        rcases hbad with ⟨hk, hr⟩
        omega
      change DAtomWeight q.1 =
        BWeight (-((q.1.1 : Int) + 1)) (-((q.1.2 : Int) + 1))
      rw [BWeight]
      simp only [if_neg hnA, if_pos hD]
      rfl

theorem kr_injective {N : Nat} : Function.Injective (@kr N) := by
  intro a b h
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          have hab : a = b := by
            apply Subtype.ext
            apply Prod.ext
            · have hf := congrArg Prod.fst h
              simp only [kr] at hf
              exact_mod_cast hf
            · have hs := congrArg Prod.snd h
              simp only [kr] at hs
              exact_mod_cast hs
          exact congrArg Sum.inl hab
      | inr b =>
          exfalso
          have hf := congrArg Prod.fst h
          simp only [kr] at hf
          omega
  | inr a =>
      cases b with
      | inl b =>
          exfalso
          have hf := congrArg Prod.fst h
          simp only [kr] at hf
          omega
      | inr b =>
          have hab : a = b := by
            apply Subtype.ext
            apply Prod.ext
            · have hf := congrArg Prod.fst h
              simp only [kr] at hf
              exact_mod_cast (show a.1.1 = b.1.1 by omega)
            · have hs := congrArg Prod.snd h
              simp only [kr] at hs
              exact_mod_cast (show a.1.2 = b.1.2 by omega)
          exact congrArg Sum.inr hab

/-- Pack an arbitrary integral cone atom into the exact finite box used by the
coefficient definition.  The branch is selected by the decidable A-cone
predicate, rather than by eliminating the proof-valued disjunction `InCones`.
-/
def packConeAtom {N : Nat} (k r : Int)
    (hc : InCones k r) (hE : E k r = (N : Int)) : PrimeFinAtom N := by
  by_cases hA : InACone k r
  · let kn := Int.toNat k
    let rn := Int.toNat r
    have hk0 : 0 ≤ k := hA.1
    have hr0 : 0 ≤ r := hA.2
    have hkcast : (kn : Int) = k := by
      simp [kn, Int.toNat_of_nonneg hk0]
    have hrcast : (rn : Int) = r := by
      simp [rn, Int.toNat_of_nonneg hr0]
    have hklt : kn < N + 1 := by
      have hbound := A_bound_k k r hk0 hr0 hE
      have hcast : (kn : Int) < ((N + 1 : Nat) : Int) := by
        rw [hkcast]
        push_cast
        omega
      exact_mod_cast hcast
    have hrlt : rn < 2 * N + 2 := by
      have hbound := A_bound_r k r hk0 hr0 hE
      have hcast : (rn : Int) < ((2 * N + 2 : Nat) : Int) := by
        rw [hrcast]
        push_cast
        omega
      exact_mod_cast hcast
    refine Sum.inl ⟨(kn, rn), ?_⟩
    simp only [AAtoms, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range]
    exact ⟨⟨hklt, hrlt⟩, by simpa [hkcast, hrcast] using hE⟩
  · have hD : InDCone k r := hc.resolve_left hA
    have hkneg : k < 0 := hD.1
    have hrneg : r < 0 := hD.2
    let m := Int.toNat (-k - 1)
    let s := Int.toNat (-r - 1)
    have hm0 : 0 ≤ -k - 1 := by omega
    have hs0 : 0 ≤ -r - 1 := by omega
    have hmcast : (m : Int) = -k - 1 := by
      dsimp only [m]
      exact Int.toNat_of_nonneg hm0
    have hscast : (s : Int) = -r - 1 := by
      dsimp only [s]
      exact Int.toNat_of_nonneg hs0
    have hkform : k = -((m : Int) + 1) := by omega
    have hrform : r = -((s : Int) + 1) := by omega
    have hmlt : m < N + 1 := by
      have hbound := D_bound_k k r hkneg hrneg hE
      have hcast : (m : Int) < ((N + 1 : Nat) : Int) := by
        rw [hmcast]
        push_cast
        omega
      exact_mod_cast hcast
    have hslt : s < 2 * N + 2 := by
      have hbound := D_bound_r k r hkneg hrneg hE
      have hcast : (s : Int) < ((2 * N + 2 : Nat) : Int) := by
        rw [hscast]
        push_cast
        omega
      exact_mod_cast hcast
    refine Sum.inr ⟨(m, s), ?_⟩
    simp only [DAtoms, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range]
    exact ⟨⟨hmlt, hslt⟩, by simpa [hkform, hrform] using hE⟩

@[simp] theorem kr_packConeAtom {N : Nat} (k r : Int)
    (hc : InCones k r) (hE : E k r = (N : Int)) :
    (packConeAtom k r hc hE).kr = (k, r) := by
  by_cases hA : InACone k r
  · simp only [packConeAtom, dif_pos hA, kr]
    apply Prod.ext
    · change (Int.toNat k : Int) = k
      exact Int.toNat_of_nonneg hA.1
    · change (Int.toNat r : Int) = r
      exact Int.toNat_of_nonneg hA.2
  · have hD : InDCone k r := hc.resolve_left hA
    have hkneg : k < 0 := hD.1
    have hrneg : r < 0 := hD.2
    simp only [packConeAtom, dif_neg hA, kr]
    apply Prod.ext
    · change -((Int.toNat (-k - 1) : Int) + 1) = k
      rw [Int.toNat_of_nonneg (show 0 ≤ -k - 1 by omega)]
      omega
    · change -((Int.toNat (-r - 1) : Int) + 1) = r
      rw [Int.toNat_of_nonneg (show 0 ≤ -r - 1 by omega)]
      omega

theorem weight_eq_one_or_neg_one {N : Nat} (a : PrimeFinAtom N) :
    a.weight = 1 ∨ a.weight = -1 := by
  cases a with
  | inl q => simpa [weight] using AAtomWeight_eq_one_or_neg_one q.1
  | inr q => simpa [weight] using DAtomWeight_eq_one_or_neg_one q.1

end PrimeFinAtom

end Ch10
end QseriesFormalization
