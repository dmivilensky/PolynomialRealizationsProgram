import jacobi.GelfandLevitan.KernelRows

/-!
Article: jacobi, Proposition C.2.
The literal finite spectral kernel sums converge to the actual F in
the original compact-domain uniform norm. Their actual continuous
spatial rows and original Hilbert row vectors retain the same uniform
error, after the genuine bounded continuous-to-L2 embedding.
Use: finiteKernelMap forms the literal finite spectral prefixes, and finiteKernelMap_limit identifies their actual uniform-norm limit with the original F.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] kernel kernelTerm

/-- An actual original spectral GL summand as a continuous kernel on the unchanged compact product domain.
Use: finiteKernelMap forms the literal finite spectral prefixes, and finiteKernelMap_limit identifies their actual uniform-norm limit with the original F.
Article: jacobi, Proposition C.2.
-/
def kernelTermMap (a : ℝ) (ha : -1<a) (k : ℕ) : C(Interval×Interval,ℝ) :=
  ⟨fun p => kernelTerm a ha k (halfTime p.1) (halfTime p.2),
    (kernelTerm_continuousOn a ha k).comp_continuous
      (g := fun p : ℝ×ℝ => kernelTerm a ha k p.1 p.2)
      (f := fun p : Interval×Interval => (halfTime p.1,halfTime p.2))
      ((halfTime.continuous.comp continuous_fst).prodMk (halfTime.continuous.comp continuous_snd))
      (fun p => ⟨halfTime_mem p.1,halfTime_mem p.2⟩)⟩

/-- The literal original finite spectral GL kernel, in its genuine uniform function norm.
Use: its genuine finite rows and finite reconstructed transformation kernels approximate the same original F and K used throughout Proposition C.2.
Article: jacobi, Proposition C.2.
-/
def finiteKernelMap (a : ℝ) (ha : -1<a) (N : ℕ) : C(Interval×Interval,ℝ) :=
  ∑ k∈Finset.range N,kernelTermMap a ha k

/-- The actual finite GL kernel evaluates to exactly its original finite spectral sum at the unchanged physical coordinates.
Use: identifies the finite operator, integral equation and differential identities with the actual prefixes of the article's original F series.
Article: jacobi, Proposition C.2.
Proof: continuous-function finite addition and evaluation preserve each genuine original kernel summand. -/
theorem finiteKernelMap_apply (a : ℝ) (ha : -1<a) (N : ℕ) (p : Interval×Interval) :
    finiteKernelMap a ha N p=∑ k∈Finset.range N,kernelTerm a ha k (halfTime p.1) (halfTime p.2) := by
  simp only [finiteKernelMap,ContinuousMap.sum_apply,kernelTermMap,ContinuousMap.coe_mk]

/-- The actual original finite GL kernel prefixes converge to the original F in the genuine compact-domain uniform norm.
Use: gives a single genuine kernel error controlling every finite source row and pointwise reconstruction simultaneously.
Article: jacobi, Proposition C.2.
Proof: pull the independently proved original uniform spectral series back to the unchanged compact physical coordinates. Their entire range lies in the proved half square; community compact-open uniform convergence is exactly convergence in the continuous-function norm. -/
theorem finiteKernelMap_limit (a : ℝ) (ha : -1<a) :
    Tendsto (finiteKernelMap a ha) atTop (𝓝 (kernelMap a ha)) := by
  -- The full original physical half square includes both singular endpoint edges; the compact coordinate pullback leaves every actual original value unchanged.
  apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
  have h := (kernel_uniform_limit a ha).comp (fun p : Interval×Interval => (halfTime p.1,halfTime p.2))
  have hset : (fun p : Interval×Interval => (halfTime p.1,halfTime p.2)) ⁻¹'
      (Icc (0:ℝ) (1/2)×ˢIcc (0:ℝ) (1/2))=univ :=
    Set.eq_univ_of_forall (fun p => ⟨halfTime_mem p.1,halfTime_mem p.2⟩)
  rw [hset,tendstoUniformlyOn_univ] at h
  change TendstoUniformly (fun (N : ℕ) (p : Interval×Interval) =>
    ∑ k∈Finset.range N,kernelTerm a ha k (halfTime p.1) (halfTime p.2))
    (fun p : Interval×Interval => kernel a ha (halfTime p.1) (halfTime p.2)) atTop at h
  simpa only [finiteKernelMap_apply,Function.comp_apply,kernelMap,ContinuousMap.coe_mk] using h

/-- The actual continuous-function-to-original-half-Hilbert-space row embedding.
Use: the original and finite kernel row vectors use the same bounded linear map, so their actual uniform error gives the genuine original L2 error.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: the community continuous-to-L2 embedding and orthogonal half-domain projection. -/
def rowEmbedding : C(Interval,ℝ) →L[ℝ] halfSubspace :=
  halfSubspace.orthogonalProjectionOnto ∘L ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume

/-- The genuine continuous spatial rows of the actual original finite spectral kernel prefix.
Use: finiteKernelRowVector forms the actual finite GL right-hand sides; their original continuous representatives enter the reconstructed K^(N).
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteKernelRows (a : ℝ) (ha : -1<a) (N : ℕ) : C(HalfInterval,C(Interval,ℝ)) :=
  (finiteKernelMap a ha N).curry.comp halfInclusion

/-- The genuine original Hilbert row of the finite spectral kernel prefix.
Use: finite inverse solution rows are computed from precisely these actual finite GL data and converge to the original inverse rows.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteKernelRowVector (a : ℝ) (ha : -1<a) (N : ℕ) : C(HalfInterval,halfSubspace) :=
  ⟨fun t => rowEmbedding (finiteKernelRows a ha N t),
    rowEmbedding.continuous.comp (finiteKernelRows a ha N).continuous⟩

/-- Every actual finite continuous row error is bounded by the same original compact-kernel uniform error.
Use: finiteKernelRowVector_error transfers the original genuine uniform spectral convergence to the original L2 row vectors, independently of the physical endpoint.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: every spatial row evaluation is evaluation of the original compact kernel difference at the same physical point; bound it by that kernel's actual supremum norm. -/
theorem finiteKernelRows_error (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval) :
    ‖finiteKernelRows a ha N t-kernelRows a ha t‖≤‖finiteKernelMap a ha N-kernelMap a ha‖ := by
  apply ((finiteKernelRows a ha N t-kernelRows a ha t).norm_le (norm_nonneg _)).mpr
  intro r
  exact (finiteKernelMap a ha N-kernelMap a ha).norm_coe_le_norm (halfInclusion t,r)

/-- The actual finite Hilbert row error is uniformly bounded by the genuine original kernel error times the norm of the same original row embedding.
Use: combines with actual uniform inverse convergence to prove convergence of the genuine finite GL inverse rows and reconstructed transformation kernels.
Article: jacobi, Proposition C.2.
Proof: original and finite Hilbert rows are the image of their true continuous rows under one fixed original bounded linear embedding. Apply its norm inequality and the actual uniform row error estimate. -/
theorem finiteKernelRowVector_error (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval) :
    ‖finiteKernelRowVector a ha N t-kernelRowVector a ha t‖≤
      ‖rowEmbedding‖*‖finiteKernelMap a ha N-kernelMap a ha‖ := by
  change ‖rowEmbedding (finiteKernelRows a ha N t)-rowEmbedding (kernelRows a ha t)‖≤_
  rw [← map_sub]
  exact (rowEmbedding.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (finiteKernelRows_error a ha N t) (norm_nonneg _))

end
end jacobi.GelfandLevitan
