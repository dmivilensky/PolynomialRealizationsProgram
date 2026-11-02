import jacobi.Analysis.CellGeometry

/-!
Article: jacobi, Theorem 2.1.
A full physical matrix error vanishes uniformly if it vanishes along
every cofinal moving pair of physical rows with convergent coordinates.
Source: compactness of the closed physical square and subsequences.
Use: the genuine Green-matrix limit becomes a uniform diagonal profile limit, sufficient for the exact finite energy limit in Theorem 2.1.
-/
namespace jacobi.Analysis
noncomputable section
open Set Filter jacobi.Reference
open scoped Topology

/-- Vanishing on every actual cofinal moving row pair implies uniform
vanishing on the entire original full physical matrix square.
Use: the genuine Green-matrix limit becomes a uniform diagonal profile
limit, sufficient for the exact finite energy limit in Theorem 2.1.
Article: jacobi, Theorem 2.1.
Proof: failure selects bad entries in cofinal actual dimensions. Their
physical coordinates have a convergent subsequence in the compact full
square; the given moving-pair limit contradicts those same bad errors. -/
theorem matrix_uniform_zero {E:Type*} [NormedAddCommGroup E]
    (f:∀n:ℕ,Fin (n+1)→Fin (n+1)→E)
    (hf:∀(ns:ℕ→ℕ),Tendsto ns atTop atTop→∀(i j:∀r:ℕ,Fin (ns r+1)),
      ∀t s:Interval,
      Tendsto (fun r:ℕ => matrixMesh (ns r) (i r)) atTop (𝓝 (t:ℝ))→
      Tendsto (fun r:ℕ => matrixMesh (ns r) (j r)) atTop (𝓝 (s:ℝ))→
      Tendsto (fun r => f (ns r) (i r) (j r)) atTop (𝓝 0)) :
    ∀ε:ℝ,0<ε→∃N:ℕ,∀n≥N,∀i j:Fin (n+1),‖f n i j‖<ε := by
  -- Retain both original dependent finite indices while taking the compact subsequence.
  classical
  intro ε hε
  by_contra h
  push Not at h
  choose ns hns is js hbad using h
  have hn : Tendsto ns atTop atTop := tendsto_atTop_mono hns tendsto_id
  let p (r:ℕ) : Interval×Interval := (matrixPoint (ns r) (is r),matrixPoint (ns r) (js r))
  obtain ⟨z,_,φ,hφ,hp⟩ := (isCompact_univ (X:=Interval×Interval)).tendsto_subseq
    (fun r => mem_univ (p r))
  have hi : Tendsto (fun r => matrixMesh (ns (φ r)) (is (φ r))) atTop (𝓝 (z.1:ℝ)) :=
    (continuous_subtype_val.comp continuous_fst).continuousAt.tendsto.comp hp
  have hj : Tendsto (fun r => matrixMesh (ns (φ r)) (js (φ r))) atTop (𝓝 (z.2:ℝ)) :=
    (continuous_subtype_val.comp continuous_snd).continuousAt.tendsto.comp hp
  have hl := hf (ns ∘ φ) (hn.comp hφ.tendsto_atTop) (fun r => is (φ r))
    (fun r => js (φ r)) z.1 z.2 hi hj
  obtain ⟨r,hr⟩ := (hl.norm.eventually (Iio_mem_nhds (by simpa only [norm_zero] using hε))).exists
  exact (not_lt_of_ge (hbad (φ r))) hr

end
end jacobi.Analysis
