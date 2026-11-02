import jacobi.GelfandLevitan.KernelBound

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
The literal source GL series is absolutely and uniformly convergent on
the whole physical half square. The actual kernel is continuous,
symmetric and zero on both singular endpoint edges. The summable
inverse-square bound includes every genuine original spectral index.
Use: absorbs the actual finite small-index prefix into the common inverse-square source kernel bound.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Complex Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Each genuine original GL summand has a finite uniform bound on the entire physical half square.
Use: absorbs the actual finite small-index prefix into the common inverse-square source kernel bound.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the genuine original summand is jointly continuous on the compact physical square. Its actual norm therefore has a finite bound; increase it to a strictly positive number. -/
theorem kernelTerm_bounded (a : ℝ) (ha : -1<a) (k : ℕ) :
    ∃ B : ℝ,0<B ∧ ∀ t∈Icc (0:ℝ) (1/2),∀ s∈Icc (0:ℝ) (1/2),|kernelTerm a ha k t s|≤B := by
  obtain ⟨B,hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (kernelTerm_continuousOn a ha k)
  refine ⟨|B|+1,by positivity,fun t ht s hs => ?_⟩
  have hh := hB (t,s) ⟨ht,hs⟩
  rw [Real.norm_eq_abs] at hh
  linarith [le_abs_self B]

/-- All genuine original GL summands satisfy one fixed positive uniform inverse-square bound, including every actual small spectral index.
Use: the original p-series majorant proves genuine absolute and uniform convergence of the source kernel.
Article: jacobi, Proposition C.2.
Proof: the true spectral tail has the proved inverse-square estimate.
Each remaining genuine summand has a compact continuous bound. A finite
sum of its scaled bounds dominates the actual finite prefix, and adding
that sum to the tail constant gives one global positive coefficient. -/
theorem kernelTerm_uniform_bound (a : ℝ) (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ k:ℕ,∀ t∈Icc (0:ℝ) (1/2),∀ s∈Icc (0:ℝ) (1/2),
      |kernelTerm a ha k t s|≤C/(k+1:ℝ)^2 := by
  -- The actual finite prefix is bounded analytically; no numerical certificate or omitted index is used.
  obtain ⟨C,hC,htail⟩ := kernelTerm_tail_bound ha
  obtain ⟨K,hK⟩ := eventually_atTop.mp htail
  choose B hBpos hB using kernelTerm_bounded a ha
  let S := ∑ j∈Finset.range K,B j*(j+1:ℝ)^2
  have hS : 0≤S := Finset.sum_nonneg (fun j _ => mul_nonneg (hBpos j).le (sq_nonneg (j+1:ℝ)))
  refine ⟨C+S,hC.trans_le (by linarith),fun k t ht s hs => ?_⟩
  by_cases hk : K≤k
  · exact (hK k hk t ht s hs).trans (div_le_div_of_nonneg_right (by linarith) (sq_nonneg (k+1:ℝ)))
  · have hi : B k*(k+1:ℝ)^2≤S := Finset.single_le_sum
      (s := Finset.range K) (f := fun j => B j*(j+1:ℝ)^2)
      (fun j _ => mul_nonneg (hBpos j).le (sq_nonneg (j+1:ℝ))) (Finset.mem_range.mpr (by omega))
    apply (le_div_iff₀ (by positivity : (0:ℝ)<(k+1:ℝ)^2)).mpr
    have hm := mul_le_mul_of_nonneg_right (hB k t ht s hs) (sq_nonneg (k+1:ℝ))
    linarith

/-- The actual source GL kernel, defined by its proved absolutely and uniformly convergent original series.
Use: supplies the genuine continuous symmetric kernel in the source quadratic identity and GL equation.
Article: jacobi, Appendix C.2 (exact parity splitting).
-/
def kernel (a : ℝ) (ha : -1<a) (t s : ℝ) : ℝ := ∑' k,kernelTerm a ha k t s

/-- The genuine original GL kernel series is absolutely summable at every point of its physical half square.
Use: justifies the original kernel definition and termwise symmetry and integral identities.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: the true full-index summands are bounded by the proved positive constant times the genuine shifted inverse-square p-series. -/
theorem kernel_absolute_summable (a : ℝ) (ha : -1<a) {t s : ℝ}
    (ht : t∈Icc 0 (1/2)) (hs : s∈Icc 0 (1/2)) :
    Summable (fun k => |kernelTerm a ha k t s|) := by
  obtain ⟨C,hC,hbound⟩ := kernelTerm_uniform_bound a ha
  have hM : Summable (fun k:ℕ => C/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left C
  exact hM.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => hbound k t ht s hs)

/-- The genuine original GL kernel is the uniform limit of its actual natural partial sums on the entire physical half square.
Use: justifies the source termwise integrals and preserves genuine joint continuity at every boundary point.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: the proved full-index inverse-square bound is one actual summable uniform majorant; apply the community uniform-series theorem. -/
theorem kernel_uniform_limit (a : ℝ) (ha : -1<a) :
    TendstoUniformlyOn
      (fun N:ℕ => fun p : ℝ × ℝ => ∑ k∈Finset.range N,kernelTerm a ha k p.1 p.2)
      (fun p : ℝ × ℝ => kernel a ha p.1 p.2) atTop
      (Icc (0:ℝ) (1/2)×ˢIcc (0:ℝ) (1/2)) := by
  obtain ⟨C,hC,hbound⟩ := kernelTerm_uniform_bound a ha
  have hM : Summable (fun k:ℕ => C/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left C
  exact tendstoUniformlyOn_tsum_nat hM (fun k p hp => by
    simpa only [Real.norm_eq_abs] using hbound k p.1 hp.1 p.2 hp.2)

/-- The genuine original GL kernel is jointly continuous on the full physical half square, including its singular endpoint edges.
Use: supplies the actual continuous source kernel in the compact operator and GL existence arguments.
Article: jacobi, Proposition C.2.
Proof: its actual natural partial sums are jointly continuous, and the original series converges uniformly on the same whole square. -/
theorem kernel_continuousOn (a : ℝ) (ha : -1<a) :
    ContinuousOn (fun p : ℝ × ℝ => kernel a ha p.1 p.2)
      (Icc (0:ℝ) (1/2)×ˢIcc (0:ℝ) (1/2)) := by
  apply (kernel_uniform_limit a ha).continuousOn
  apply Filter.Frequently.of_forall
  intro N
  exact continuousOn_finsetSum _ (fun k _ => kernelTerm_continuousOn a ha k)

/-- The genuine original uniformly convergent source GL kernel is symmetric.
Use: the actual kernel integral operator is self-adjoint in the source positivity and GL equation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: every actual original summand is symmetric; the two genuine infinite sums agree term by term. -/
theorem kernel_symmetric (a : ℝ) (ha : -1<a) (t s : ℝ) : kernel a ha t s=kernel a ha s t := by
  exact tsum_congr (fun k => kernelTerm_symmetric a ha k t s)

/-- The actual source GL kernel vanishes on its singular left edge.
Use: fixes the genuine zero endpoint data in the original GL equation and transformed selected branch.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: every genuine original summand vanishes at that endpoint. -/
theorem kernel_zero (a : ℝ) (ha : -1<a) (s : ℝ) : kernel a ha 0 s=0 := by
  simp only [kernel,kernelTerm_zero,tsum_zero]

end
end jacobi.GelfandLevitan
