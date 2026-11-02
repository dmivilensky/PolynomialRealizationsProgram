import jacobi.Analysis.MatrixCompactness

/-!
Article: jacobi, Theorem C.5.
Cofinal moving-row convergence with every convergent compact parameter
sequence gives a uniform actual finite-array limit in both variables.
Source: sequential compactness of the physical interval times the parameter set.
Use: Theorem C.5's actual shifted diagonal converges uniformly over its complete physical matrix range and every original compact shift set.
-/
namespace jacobi.Analysis
noncomputable section
open Set Filter jacobi.Reference
open scoped Topology

/-- Vanishing along every cofinal physical row and convergent compact
parameter sequence implies full uniform finite-array vanishing.
Use: Theorem C.5's actual shifted diagonal converges uniformly over its
complete physical matrix range and every original compact shift set.
Article: jacobi, Theorem C.5.
Proof: a failure selects bad entries and parameters at cofinal genuine
dimensions. Their actual physical coordinates and parameters have a
common convergent subsequence; the moving limit contradicts badness. -/
theorem parameter_matrix_uniform_zero {P E:Type*} [MetricSpace P] [CompactSpace P]
    [NormedAddCommGroup E] (f:∀n:ℕ,Fin (n+1)→P→E)
    (hf:∀(ns:ℕ→ℕ),Tendsto ns atTop atTop→∀(i:∀r:ℕ,Fin (ns r+1)),
      ∀t:Interval,Tendsto (fun r => matrixMesh (ns r) (i r)) atTop (𝓝 (t:ℝ))→
      ∀p:ℕ→P,∀p0:P,Tendsto p atTop (𝓝 p0)→
      Tendsto (fun r => f (ns r) (i r) (p r)) atTop (𝓝 0)) :
    ∀ε:ℝ,0<ε→∃N:ℕ,∀n≥N,∀i:Fin (n+1),∀p:P,‖f n i p‖<ε := by
  -- The selected bad row and actual parameter remain coupled on the compact subsequence.
  classical
  intro ε hε
  by_contra h
  push Not at h
  choose ns hns is ps hbad using h
  have hn : Tendsto ns atTop atTop := tendsto_atTop_mono hns tendsto_id
  let q (r:ℕ) : Interval×P := (matrixPoint (ns r) (is r),ps r)
  obtain ⟨z,_,φ,hφ,hq⟩ := (isCompact_univ (X:=Interval×P)).tendsto_subseq (fun r => mem_univ (q r))
  have hi : Tendsto (fun r => matrixMesh (ns (φ r)) (is (φ r))) atTop (𝓝 (z.1:ℝ)) :=
    (continuous_subtype_val.comp continuous_fst).continuousAt.tendsto.comp hq
  have hp : Tendsto (fun r => ps (φ r)) atTop (𝓝 z.2) := continuous_snd.continuousAt.tendsto.comp hq
  have hl := hf (ns ∘ φ) (hn.comp hφ.tendsto_atTop) (fun r => is (φ r)) z.1 hi (ps ∘ φ) z.2 hp
  obtain ⟨r,hr⟩ := (hl.norm.eventually (Iio_mem_nhds (by simpa only [norm_zero] using hε))).exists
  exact (not_lt_of_ge (hbad (φ r))) hr

end
end jacobi.Analysis
