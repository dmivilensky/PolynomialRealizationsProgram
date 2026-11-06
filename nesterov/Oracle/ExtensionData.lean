import nesterov.Oracle.Simplex
import polyak.Interpolation.Conjugate

/-! A concrete smooth strongly convex extension defined by a finite
simplex maximum. This is the normalized DT22 construction. -/
namespace nesterov.Oracle
noncomputable section
open Set Filter
open scoped Topology BigOperators

structure ExtensionData (I E : Type*) where
  q : ℝ
  q_pos : 0<q
  q_lt_one : q<1
  slopes : I→E
  offsets : I→ℝ

namespace ExtensionData
variable {I E : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : ExtensionData I E)

def raw (y : E) (α : I→ℝ) : ℝ :=
  inner ℝ (moment D.slopes α) y-‖moment D.slopes α‖^2/(2*(1-D.q))+height D.offsets α

omit [DecidableEq I] [Nonempty I] in
theorem continuous_raw (y : E) : Continuous (D.raw y) := by
  unfold raw
  exact ((continuous_moment D.slopes).inner continuous_const |>.sub
    ((continuous_moment D.slopes).norm.pow 2 |>.div_const _)).add (continuous_height D.offsets)

theorem exists_optimizer (y : E) :
    ∃ α∈Weights I,∀ β∈Weights I,D.raw y β≤D.raw y α := by
  have hn : (Weights I).Nonempty := ⟨Pi.single (Classical.arbitrary I) 1,weights_single _⟩
  obtain ⟨α,hα,hm⟩ := weights_compact.exists_isMaxOn hn (D.continuous_raw y).continuousOn
  exact ⟨α,hα,hm⟩

def optimizer (y : E) : I→ℝ := Classical.choose (D.exists_optimizer y)

theorem optimizer_weights (y : E) : D.optimizer y∈Weights I :=
  (Classical.choose_spec (D.exists_optimizer y)).1

theorem optimizer_max (y : E) (β : I→ℝ) (hβ : β∈Weights I) :
    D.raw y β≤D.raw y (D.optimizer y) :=
  (Classical.choose_spec (D.exists_optimizer y)).2 β hβ

def support (y : E) : E := moment D.slopes (D.optimizer y)
def potential (y : E) : ℝ := D.q/2*‖y‖^2+D.raw y (D.optimizer y)
def field (y : E) : E := D.q • y+D.support y

omit [DecidableEq I] [Nonempty I] in
theorem raw_mix (y : E) (α β : I→ℝ) (t : ℝ) :
    D.raw y ((1-t) • α+t • β)=
      (1-t)*D.raw y α+t*D.raw y β+
        t*(1-t)*‖moment D.slopes β-moment D.slopes α‖^2/(2*(1-D.q)) := by
  simp only [raw,moment_mix,height_mix,inner_add_left,real_inner_smul_left,
    polyak.Interpolation.norm_mix_sq,norm_sub_rev (moment D.slopes α)]
  ring

end ExtensionData

theorem linear_nonpos_of_quadratic (A B : ℝ)
    (h : ∀ t∈Icc (0:ℝ) 1,t*A-t^2*B≤0) : A≤0 := by
  have ht : Tendsto (fun t : ℝ=>t*B) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hi : Tendsto (id : ℝ→ℝ) (𝓝[>] (0:ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [id_eq,zero_mul] using hi.mul_const B
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t htp ht1
  have hb := h t ⟨htp.le,ht1.le⟩
  have he : t*(A-t*B)≤0 := by nlinarith
  have hh : A-t*B≤0 := by
    by_contra hn
    have hp := mul_pos htp (lt_of_not_ge hn)
    linarith
  linarith

namespace ExtensionData
variable {I E : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : ExtensionData I E)

omit [DecidableEq I] [Nonempty I] in
theorem max_strong {y : E} {α : I→ℝ} (hα : α∈Weights I)
    (hm : ∀ β∈Weights I,D.raw y β≤D.raw y α) {β : I→ℝ} (hβ : β∈Weights I) :
    D.raw y β+‖moment D.slopes β-moment D.slopes α‖^2/(2*(1-D.q))≤D.raw y α := by
  have h := linear_nonpos_of_quadratic
    (D.raw y β-D.raw y α+‖moment D.slopes β-moment D.slopes α‖^2/(2*(1-D.q)))
    (‖moment D.slopes β-moment D.slopes α‖^2/(2*(1-D.q))) (by
      intro t ht
      have hh := hm _ (weights_mix hα hβ ht)
      rw [D.raw_mix] at hh
      convert sub_nonpos.mpr hh using 1
      ring)
  linarith

theorem optimizer_strong (y : E) {β : I→ℝ} (hβ : β∈Weights I) :
    D.raw y β+‖moment D.slopes β-D.support y‖^2/(2*(1-D.q))≤D.raw y (D.optimizer y) :=
  D.max_strong (D.optimizer_weights y) (D.optimizer_max y) hβ

end ExtensionData
end
end nesterov.Oracle
