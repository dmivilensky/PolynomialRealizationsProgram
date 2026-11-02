import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sigma

/-!
Article: main_krylov, apG:flat, genuine dyadic decomposition of the prefix relation.
Use: construct the actual dyadic rectangles in the ordered coordinate set.
Every strict prefix pair belongs to exactly one rectangle level, namely its
most significant differing bit. The subsequent nuclear estimate can therefore
use a real decomposition, rather than an assumed dyadic representation.
Source: standard binary prefix partition; mathlib's actual most significant
bit theorem and bitwise comparison.
-/

namespace krylov.Tensor
open Set

/-- Equality of actual upper binary prefixes is exactly equality of all higher bits.
Article: main_krylov, apG:flat, genuine dyadic block dictionary. -/
theorem shiftRight_succ_eq_iff (a b k : ℕ) :
    a >>> (k + 1) = b >>> (k + 1) ↔ ∀ j, k < j → a.testBit j = b.testBit j := by
  constructor
  · intro h j hj
    have he := congrArg (fun x : ℕ => x.testBit (j - (k + 1))) h
    simpa only [Nat.testBit_shiftRight, Nat.add_sub_cancel' (by omega : k + 1 ≤ j)] using he
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    simpa only [Nat.testBit_shiftRight] using h (k + 1 + j) (by omega)

/-- The actual strict-prefix relation splits into unique dyadic rectangles indexed by their first differing bit.
Article: main_krylov, apG:flat, genuine dyadic prefix decomposition.
Proof: take the actual most significant set bit of the nonzero xor. Its
orientation follows from the original order, and all higher bits agree.
Conversely binary comparison gives strict order; two different levels would
force their higher differing bit to be simultaneously equal and unequal. -/
theorem dyadic_prefix_unique (L a b : ℕ) (_ha : a < 2 ^ L) (hb : b < 2 ^ L) :
    a < b ↔ ∃! k : ℕ, k < L ∧ a.testBit k = false ∧ b.testBit k = true ∧
      a >>> (k + 1) = b >>> (k + 1) := by
  constructor
  · intro hab
    have hxor : a ^^^ b ≠ 0 := Nat.xor_ne_zero_iff.mpr hab.ne
    obtain ⟨k, hk, hhigh⟩ := Nat.exists_most_significant_bit hxor
    have hh : ∀ j, k < j → a.testBit j = b.testBit j := by
      intro j hj
      have h := hhigh j hj
      rw [Nat.testBit_xor] at h
      exact bne_eq_false_iff_eq.mp h
    have hbits : a.testBit k = false ∧ b.testBit k = true := by
      cases hka : a.testBit k <;> cases hkb : b.testBit k
      · simp only [Nat.testBit_xor, hka, hkb, bne_self_eq_false] at hk
        contradiction
      · exact ⟨rfl, rfl⟩
      · exact (hab.not_gt (Nat.lt_of_testBit k hkb hka (fun j hj => (hh j hj).symm))).elim
      · simp only [Nat.testBit_xor, hka, hkb, bne_self_eq_false] at hk
        contradiction
    have hkL : k < L := by
      by_contra h
      have hLk : L ≤ k := by omega
      have hp : 2 ^ L ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hLk
      have hz := Nat.testBit_eq_false_of_lt (hb.trans_le hp)
      rw [hbits.2] at hz
      contradiction
    refine ⟨k, ⟨hkL, hbits.1, hbits.2, (shiftRight_succ_eq_iff a b k).mpr hh⟩, ?_⟩
    intro j hj
    rcases lt_trichotomy j k with hjk | rfl | hkj
    · have he := (shiftRight_succ_eq_iff a b j).mp hj.2.2.2 k hjk
      rw [hbits.1, hbits.2] at he
      contradiction
    · rfl
    · have he := hh j hkj
      rw [hj.2.1, hj.2.2.1] at he
      contradiction
  · rintro ⟨k, hk, _⟩
    exact Nat.lt_of_testBit k hk.2.1 hk.2.2.1 ((shiftRight_succ_eq_iff a b k).mp hk.2.2.2)

/-- The actual left or right half of a binary block in the original finite coordinate set.
Article: main_krylov, apG:flat, the true dyadic block family. -/
def dyadicHalf (N k r : ℕ) (bit : Bool) : Finset (Fin N) :=
  Finset.univ.filter (fun a => a.val >>> (k + 1) = r ∧ a.val.testBit k = bit)

/-- At any fixed level, different actual dyadic blocks are disjoint.
Article: main_krylov, apG:flat, genuine level partition. -/
theorem dyadicHalf_disjoint (N k r s : ℕ) (bit : Bool) (hrs : r ≠ s) :
    Disjoint (dyadicHalf N k r bit) (dyadicHalf N k s bit) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  simp only [dyadicHalf, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact hrs (ha.1.symm.trans hb.1)

/-- Two actual dyadic half-blocks at different levels are nested whenever they meet.
Article: main_krylov, apG:flat, the actual unique-coarse-intersection property.
Proof: all bits above the finer level agree in a real finer block. In
particular, every bit defining the coarser block agrees at every fine point. -/
theorem dyadicHalf_subset_of_inter (N k l r s : ℕ) (bit coarse : Bool) (hkl : k < l)
    (hmeet : (dyadicHalf N k r bit ∩ dyadicHalf N l s coarse).Nonempty) :
    dyadicHalf N k r bit ⊆ dyadicHalf N l s coarse := by
  obtain ⟨a, ha⟩ := hmeet
  have ha' := Finset.mem_inter.mp ha
  have haf := Finset.mem_filter.mp ha'.1
  have hac := Finset.mem_filter.mp ha'.2
  intro b hb
  have hbf := Finset.mem_filter.mp hb
  have hprefix : b.val >>> (k + 1) = a.val >>> (k + 1) := hbf.2.1.trans haf.2.1.symm
  have hbits := (shiftRight_succ_eq_iff b.val a.val k).mp hprefix
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · exact ((shiftRight_succ_eq_iff b.val a.val l).mpr (fun j hj => hbits j (by omega))).trans hac.2.1
  · exact (hbits l hkl).trans hac.2.2

/-- A genuine dyadic half-block contains at most its actual dyadic length many coordinates.
Article: main_krylov, apG:flat, true dyadic block sizes.
Proof: the lower k bits inject the actual half-block into Fin(2^k), since
its kth bit and all higher bits are fixed by the real block definition. -/
theorem dyadicHalf_card_le (N k r : ℕ) (bit : Bool) :
    (dyadicHalf N k r bit).card ≤ 2 ^ k := by
  let low : Fin N → Fin (2 ^ k) := fun a => ⟨a.val % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩
  have hinj : Set.InjOn low (dyadicHalf N k r bit) := by
    intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    have hprefix : a.val >>> (k + 1) = b.val >>> (k + 1) := ha'.1.trans hb'.1.symm
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro j
    rcases lt_trichotomy j k with hj | rfl | hj
    · have hlow := congrArg (fun x : Fin (2 ^ k) => x.val.testBit j) hab
      simpa only [low, Nat.testBit_mod_two_pow, hj, decide_true, Bool.true_and] using hlow
    · exact ha'.2.trans hb'.2.symm
    · exact (shiftRight_succ_eq_iff a.val b.val k).mp hprefix j hj
  have hc := Finset.card_le_card_of_injOn low (s := dyadicHalf N k r bit)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _) hinj
  simpa only [Finset.card_univ, Fintype.card_fin] using hc

/-- Every actual upper binary prefix has the correct finite dyadic block index.
Article: main_krylov, apG:flat, the true number of blocks at a level. -/
theorem dyadic_prefix_index_lt (L m k : ℕ) (hm : m < 2 ^ L) (hk : k < L) :
    m >>> (k + 1) < 2 ^ (L - (k + 1)) := by
  rw [Nat.shiftRight_eq_div_pow]
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos (k + 1))).mpr
  simpa only [← Nat.pow_add, Nat.sub_add_cancel (by omega : k + 1 ≤ L)] using hm

/-- The genuine finite dyadic rectangle indices, with their true level-dependent block counts.
Article: main_krylov, apG:flat, actual dyadic decomposition indices. -/
abbrev DyadicPrefixIndex (L : ℕ) := (k : Fin L) × Fin (2 ^ (L - (k.val + 1)))

/-- Every actual ordered prefix pair belongs to exactly one genuine finite dyadic rectangle.
Article: main_krylov, apG:flat, real dyadic tensor decomposition.
Proof: the genuine most-significant-bit partition chooses its actual level;
the actual common higher prefix chooses its unique finite block index. -/
theorem dyadic_prefix_rectangle_unique (N L : ℕ) (hN : N ≤ 2 ^ L) (a b : Fin N) :
    a < b ↔ ∃! p : DyadicPrefixIndex L,
      a ∈ dyadicHalf N p.1.val p.2.val false ∧ b ∈ dyadicHalf N p.1.val p.2.val true := by
  have ha : a.val < 2 ^ L := a.isLt.trans_le hN
  have hb : b.val < 2 ^ L := b.isLt.trans_le hN
  constructor
  · intro hab
    obtain ⟨k, hk, huniq⟩ := (dyadic_prefix_unique L a.val b.val ha hb).mp hab
    let kf : Fin L := ⟨k, hk.1⟩
    let rf : Fin (2 ^ (L - (kf.val + 1))) := ⟨b.val >>> (k + 1), dyadic_prefix_index_lt L b.val k hb hk.1⟩
    refine ⟨⟨kf, rf⟩, ?_, ?_⟩
    · simp only [dyadicHalf, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨hk.2.2.2, hk.2.1⟩, ⟨rfl, hk.2.2.1⟩⟩
    · rintro ⟨j, s⟩ ⟨haj, hbj⟩
      have haj' := (Finset.mem_filter.mp haj).2
      have hbj' := (Finset.mem_filter.mp hbj).2
      have hj : j.val = k := huniq j.val ⟨j.isLt, haj'.2, hbj'.2, haj'.1.trans hbj'.1.symm⟩
      have hjf : j = kf := Fin.ext hj
      subst j
      have hs : s = rf := Fin.ext hbj'.1.symm
      subst s
      rfl
  · rintro ⟨⟨k, r⟩, ⟨ha', hb'⟩, _⟩
    have hak := (Finset.mem_filter.mp ha').2
    have hbk := (Finset.mem_filter.mp hb').2
    exact Nat.lt_of_testBit k.val hak.2 hbk.2
      ((shiftRight_succ_eq_iff a.val b.val k.val).mp (hak.1.trans hbk.1.symm))

/-- Every genuine dyadic rectangle lies in the actual strict prefix relation.
Article: main_krylov, apG:flat, ordered dyadic decomposition. -/
theorem dyadic_rectangle_lt {N k r : ℕ} {a b : Fin N}
    (ha : a ∈ dyadicHalf N k r false) (hb : b ∈ dyadicHalf N k r true) : a < b := by
  have ha' := (Finset.mem_filter.mp ha).2
  have hb' := (Finset.mem_filter.mp hb).2
  exact Nat.lt_of_testBit k ha'.2 hb'.2
    ((shiftRight_succ_eq_iff a.val b.val k).mp (ha'.1.trans hb'.1.symm))

/-- Actual dyadic half-blocks are nested upon intersection also at equal levels.
Article: main_krylov, apG:flat, all ordered level pairs. -/
theorem dyadicHalf_subset_of_inter_le (N k l r s : ℕ) (bit : Bool) (hkl : k ≤ l)
    (hmeet : (dyadicHalf N k r bit ∩ dyadicHalf N l s bit).Nonempty) :
    dyadicHalf N k r bit ⊆ dyadicHalf N l s bit := by
  rcases hkl.eq_or_lt with rfl | hkl
  · obtain ⟨a, ha⟩ := hmeet
    have ha' := Finset.mem_inter.mp ha
    have hr : r = s := ((Finset.mem_filter.mp ha'.1).2.1).symm.trans ((Finset.mem_filter.mp ha'.2).2.1)
    subst s
    exact Finset.Subset.refl _
  · exact dyadicHalf_subset_of_inter N k l r s bit bit hkl hmeet

end krylov.Tensor
