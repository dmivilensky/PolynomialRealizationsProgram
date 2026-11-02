import jacobi.Comparison.GreenLimit
import jacobi.Analysis.MatrixCompactness

/-!
Article: jacobi, Theorem 2.1.
The genuine normalized target Green matrix converges uniformly on
its full physical square to the original continuous Green kernel.
In particular its full diagonal uniformly approximates phi_alpha.
Use: the original diagonal profile and finite energy limit of Theorem 2.1 follow from this actual estimate with no additional bound premise.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan
open scoped Topology

/-- The actual full target Green matrix converges uniformly on the
entire original physical matrix square to twice its genuine Green kernel.
Use: the original diagonal profile and finite energy limit of Theorem 2.1
follow from this actual estimate with no additional bound premise.
Article: jacobi, Theorem 2.1.
Proof: every cofinal moving pair has the independently proved true
Green limit. The genuine continuous Green kernel has the same moving
sample limit; compactness of the original physical square makes the
actual difference uniformly small, retaining both endpoints. -/
theorem scaledTargetGreen_uniform {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∀ε:ℝ,0<ε→∃N:ℕ,∀n≥N,∀i j:Fin (n+1),
      |scaledTargetGreen a b ha hb n i j-
        2*targetGreenKernel a ha (matrixPoint n i) (matrixPoint n j)|<ε := by
  -- Uniformity uses the original inverse matrix and the already identified original continuum kernel.
  let err (n:ℕ) (i j:Fin (n+1)) := scaledTargetGreen a b ha hb n i j-
    2*targetGreenKernel a ha (matrixPoint n i) (matrixPoint n j)
  have hu := matrix_uniform_zero err (by
    intro ns hns i j t s hit hjs
    have hi : Tendsto (fun r => matrixPoint (ns r) (i r)) atTop (𝓝 t) := tendsto_subtype_rng.mpr hit
    have hj : Tendsto (fun r => matrixPoint (ns r) (j r)) atTop (𝓝 s) := tendsto_subtype_rng.mpr hjs
    have hk := ((targetGreenKernelMap a ha).continuous.continuousAt.tendsto.comp (hi.prodMk_nhds hj)).const_mul 2
    have hg := scaledTargetGreen_limit ha hb ns hns i j hit hjs
    simpa only [err,targetGreenKernel,Function.comp_def,sub_self] using hg.sub hk)
  simpa only [Real.norm_eq_abs] using hu

/-- The actual full target diagonal converges uniformly to its original
persymmetric profile at every original physical matrix sample.
Use: Theorem 2.1's diagonal bound and energy convergence use this exact
whole-chain approximation, including the physical middle row.
Article: jacobi, Theorem 2.1.
Proof: restrict the proved actual full Green approximation to its
diagonal and insert the already proved original Green diagonal identity. -/
theorem scaledTargetDiagonal_uniform {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∀ε:ℝ,0<ε→∃N:ℕ,∀n≥N,∀i:Fin (n+1),
      |scaledTargetGreen a b ha hb n i i-persymmetricProfile a ha (matrixPoint n i)|<ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := scaledTargetGreen_uniform ha hb ε hε
  refine ⟨N,fun n hn i => ?_⟩
  simpa only [targetGreen_diagonal,mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)] using hN n hn i i

/-- The original normalized target diagonals are uniformly bounded
at every dimension, including the entire finite initial prefix.
Use: this is the full supremum assertion of Theorem 2.1, without an
asymptotic-only bound or independently assumed small-dimension checks.
Article: jacobi, Theorem 2.1.
Proof: the true continuous profile and a uniform error below one bound
all sufficiently large dimensions. A finite sum of the absolute actual
entries bounds the finitely many remaining original dimensions. -/
theorem scaledTargetDiagonal_bound {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C:ℝ,0<C ∧ ∀n:ℕ,∀i:Fin (n+1),|scaledTargetGreen a b ha hb n i i|≤C := by
  -- The finite prefix is absorbed exactly; no numerical computation is involved.
  classical
  obtain ⟨N,hN⟩ := scaledTargetDiagonal_uniform ha hb 1 (by norm_num)
  let B := ∑n∈Finset.range N,∑i:Fin (n+1),|scaledTargetGreen a b ha hb n i i|
  refine ⟨B+‖persymmetricProfile a ha‖+1,by dsimp [B]; positivity,fun n i => ?_⟩
  have hB : 0≤B := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  by_cases hn:N≤n
  · have hh := abs_sub_le (scaledTargetGreen a b ha hb n i i) (persymmetricProfile a ha (matrixPoint n i)) 0
    simp only [sub_zero] at hh
    have hp := (persymmetricProfile a ha).norm_coe_le_norm (matrixPoint n i)
    rw [Real.norm_eq_abs] at hp
    linarith [hN n hn i]
  · have hs : |scaledTargetGreen a b ha hb n i i|≤B :=
      (Finset.single_le_sum (fun j _ => abs_nonneg (scaledTargetGreen a b ha hb n j j)) (Finset.mem_univ i)).trans
        (Finset.single_le_sum (f:=fun m:ℕ => ∑j:Fin (m+1),|scaledTargetGreen a b ha hb m j j|)
          (fun m _ => Finset.sum_nonneg (fun j _ => abs_nonneg
          (scaledTargetGreen a b ha hb m j j))) (Finset.mem_range.mpr (lt_of_not_ge hn)))
    exact hs.trans (by linarith [norm_nonneg (persymmetricProfile a ha)])

end
end jacobi.Comparison
