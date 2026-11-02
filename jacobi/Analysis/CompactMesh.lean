import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

/-!
Compactness for arbitrary closed ranges of physical mesh ratios.
Convergence along every cofinal moving mesh is enough for uniform
convergence on that range and hence a common bound for all mesh values.
Use: the genuine standard Jacobi conductance limits supply the dominated
tail meshes, without postulating an independent uniform estimate.
Article: jacobi, Theorem 5.4.
Article role: the compactness step from moving-mesh to uniform Green-kernel limits.
Source: Heine-Borel and sequential compactness of real compact intervals; mathlib real topology.
-/
namespace jacobi.Analysis
noncomputable section
open Set Filter
open scoped Topology

/-- Vanishing on every cofinal moving mesh implies uniform vanishing
on a compact interval of mesh ratios. Bad indices would have a convergent
subsequence in that same interval and contradict the moving limit.
Article: jacobi, Theorem 5.4.
Source: Heine-Borel and sequential compactness of real compact intervals; mathlib real topology.
-/
theorem compact_mesh_uniform_zero {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → ℕ → E) (a b : ℝ)
    (hf : ∀ n m : ℕ → ℕ,∀ t∈Icc a b,Tendsto n atTop atTop →
      Tendsto (fun i => (m i:ℝ)/(n i:ℝ)) atTop (𝓝 t) →
      (∀ i,(m i:ℝ)/(n i:ℝ)∈Icc a b) →
      Tendsto (fun i => f (n i) (m i)) atTop (𝓝 0)) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ n≥N,∀ m : ℕ,(m:ℝ)/(n:ℝ)∈Icc a b → ‖f n m‖<ε := by
  classical
  intro ε hε
  by_contra h
  push Not at h
  choose ns hns ms hmesh hbad using h
  have hn := tendsto_atTop_mono hns tendsto_id
  obtain ⟨t,ht,φ,hφ,hratio⟩ := isCompact_Icc.tendsto_subseq hmesh
  have hlim := hf (ns ∘ φ) (ms ∘ φ) t ht (hn.comp hφ.tendsto_atTop) hratio
    (fun i => hmesh (φ i))
  obtain ⟨i,hi⟩ := (hlim.norm.eventually
    (Iio_mem_nhds (by simpa only [norm_zero] using hε))).exists
  exact (not_lt_of_ge (hbad (φ i))) hi

/-- A continuous actual moving-mesh limit is uniform on every compact
ratio interval. The conclusion concerns all indices in each true finite
mesh, rather than a preselected sequence of indices.
Article: jacobi, Theorem 5.4.
Source: Heine-Borel and sequential compactness of real compact intervals; mathlib real topology.
-/
theorem compact_mesh_uniform_limit {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → ℕ → E) (f : ℝ → E) (a b : ℝ)
    (hc : ∀ t∈Icc a b,ContinuousAt f t)
    (hf : ∀ n m : ℕ → ℕ,∀ t∈Icc a b,Tendsto n atTop atTop →
      Tendsto (fun i => (m i:ℝ)/(n i:ℝ)) atTop (𝓝 t) →
      Tendsto (fun i => F (n i) (m i)) atTop (𝓝 (f t))) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ n≥N,∀ m : ℕ,(m:ℝ)/(n:ℝ)∈Icc a b →
      ‖F n m-f ((m:ℝ)/(n:ℝ))‖<ε := by
  apply compact_mesh_uniform_zero
  intro n m t ht hn hm _
  have h := (hf n m t ht hn hm).sub ((hc t ht).tendsto.comp hm)
  simpa only [sub_self,Function.comp_def] using h

/-- The same hypotheses give a genuine common bound on the whole
compact moving mesh. This supplies a constant dominating tail sums.
Article: jacobi, Theorem 5.4.
Source: Heine-Borel and sequential compactness of real compact intervals; mathlib real topology.
-/
theorem compact_mesh_bound {E : Type*} [NormedAddCommGroup E]
    (F : ℕ → ℕ → E) (f : ℝ → E) (a b : ℝ)
    (hc : ∀ t∈Icc a b,ContinuousAt f t)
    (hf : ∀ n m : ℕ → ℕ,∀ t∈Icc a b,Tendsto n atTop atTop →
      Tendsto (fun i => (m i:ℝ)/(n i:ℝ)) atTop (𝓝 t) →
      Tendsto (fun i => F (n i) (m i)) atTop (𝓝 (f t))) :
    ∃ B : ℝ,0<B ∧ ∃ N : ℕ,∀ n≥N,∀ m : ℕ,(m:ℝ)/(n:ℝ)∈Icc a b → ‖F n m‖≤B := by
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (show ContinuousOn f (Icc a b) from fun t ht => (hc t ht).continuousWithinAt)
  obtain ⟨N,hN⟩ := compact_mesh_uniform_limit F f a b hc hf 1 (by norm_num)
  refine ⟨max B 0+1,by linarith [le_max_right B 0],N,?_⟩
  intro n hn m hm
  have h := norm_add_le (F n m-f ((m:ℝ)/(n:ℝ))) (f ((m:ℝ)/(n:ℝ)))
  rw [sub_add_cancel] at h
  exact h.trans ((add_le_add (hN n hn m hm).le (hB _ hm)).trans
    (by linarith [le_max_left B 0]))

end
end jacobi.Analysis
