import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! Uniform strict perturbation on the complete compact frequency domain. -/
noncomputable section
namespace polyak.Levels.Geometry
open Set

theorem compact_strict_perturbation {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f g : C(X,ℝ)) (hf : ∀x,f x≤0) (hg : ∀x,f x=0→g x<0) :
    ∃ε : ℝ,0<ε ∧ ∀x,f x+ε*g x<0 := by
  let K : Set X:={x | 0≤g x}
  have hK : IsCompact K:=(isClosed_le continuous_const g.continuous).isCompact
  by_cases hn : K.Nonempty
  · obtain ⟨a,ha,hmax⟩:=hK.exists_isMaxOn hn f.continuous.continuousOn
    have hfa : f a<0 := by
      apply lt_of_le_of_ne (hf a)
      intro he
      exact (not_lt_of_ge ha) (hg a he)
    let δ:ℝ:= -f a
    let M:ℝ:=‖g‖+1
    have hδ : 0<δ:=neg_pos.mpr hfa
    have hM : 0<M:=by dsimp [M]; positivity
    refine ⟨δ/(2*M),by positivity,fun x=>?_⟩
    by_cases hx : x∈K
    · have hfx : f x≤-δ:=by
        have hh:=hmax hx
        change f x≤f a at hh
        dsimp [δ]
        linarith
      have hgx : g x≤M := by
        have hh:=ContinuousMap.norm_coe_le_norm g x
        have hb : g x≤‖g x‖:=le_abs_self _
        dsimp [M]
        linarith
      have he : δ/(2*M)*M=δ/2:=by field_simp
      have hb:=mul_le_mul_of_nonneg_left hgx (show 0≤δ/(2*M) by positivity)
      rw [he] at hb
      linarith
    · have hneg : g x<0:=lt_of_not_ge hx
      have hp : δ/(2*M)*g x<0:=mul_neg_of_pos_of_neg (by positivity) hneg
      linarith [hf x]
  · refine ⟨1,by norm_num,fun x=>?_⟩
    have hneg : g x<0:=by by_contra hh; exact hn ⟨x,le_of_not_gt hh⟩
    linarith [hf x]

end polyak.Levels.Geometry
