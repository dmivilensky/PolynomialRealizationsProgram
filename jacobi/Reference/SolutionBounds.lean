import jacobi.Reference.HighFrequency
import jacobi.Reference.EnergyDisks
import jacobi.Reference.SpectralAnalytic
import jacobi.Reference.SolutionReality
import jacobi.Reference.SolutionEndpoint

/-!
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
The actual reference solution is uniformly bounded on unit complex
energy disks at high positive shifted energy. Its genuine energy
derivative has the same bound by Cauchy's formula. The mean value
theorem then controls differences of the original real-energy solutions,
which is sufficient for the uniform GL kernel series estimate.
Use: bounds the genuine source GL summands and provides actual Cauchy-circle bounds for energy perturbations.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual reference solution has one uniform inverse-frequency bound on every original unit complex energy disk with a prescribed positive frequency scale.
Use: bounds the genuine source GL summands and provides actual Cauchy-circle bounds for energy perturbations.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the genuine energy square root stays above the given frequency
scale and in the fixed imaginary strip. Apply the proved actual
high-frequency amplitude, use the positive source exponent and bound
the exact imaginary-frequency exponential on the physical half interval. -/
theorem solution_energy_disk_bound {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ E r:ℝ,1≤r → r^2+1≤E- jacobi.Jacobi.endpointCorrection a →
      ∀ z∈Metric.closedBall (E:ℂ) 1,∀ t∈Icc (0:ℝ) (1/2),
        ‖solution a z t‖≤C*r^(-gamma a) := by
  -- All frequency hypotheses are proved for the actual square root of each original complex energy.
  obtain ⟨B,hB,hbound⟩ := wave_uniform_high_frequency ha
  refine ⟨B*Real.exp 1,by positivity,fun E r hr hE z hz t ht => ?_⟩
  obtain ⟨hscale,him⟩ := reference_energy_disk hr hE hz
  let omega := Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))
  have hrp : 0<r := lt_of_lt_of_le zero_lt_one hr
  have homega : 1≤‖omega‖ := hr.trans hscale
  have hp : ‖omega‖^(-gamma a)≤r^(-gamma a) := by
    exact Real.rpow_le_rpow_of_nonpos hrp hscale (by linarith [(parameters ha).1])
  have hexp : Real.exp (t*|omega.im|)≤Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left him ht.1
    nlinarith [ht.2]
  have hh := hbound omega homega t ht
  change ‖solution a z t‖≤B*‖omega‖^(-gamma a)*Real.exp (t*|omega.im|) at hh
  apply hh.trans
  have hmul := mul_le_mul hp hexp (Real.exp_pos _).le (Real.rpow_pos_of_pos hrp _).le
  nlinarith [mul_le_mul_of_nonneg_left hmul hB.le]

/-- The genuine original reference energy function is entire at every physical half-interval point, including zero.
Use: Cauchy's formula for the actual source energy derivative has no excluded spatial endpoint.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: interior points use the actual polynomial-coefficient energy series. At zero the original positive-exponent prefactor makes the function identically zero. -/
theorem solution_energy_analytic_half {a : ℝ} (ha : -1<a) {t : ℝ}
    (ht : t∈Icc 0 (1/2)) (z : ℂ) : AnalyticAt ℂ (fun z => solution a z t) z := by
  by_cases h : t=0
  · subst t
    have he : (fun z => solution a z 0)=(fun _ => (0:ℂ)) := funext (solution_zero ha)
    rw [he]
    exact analyticAt_const
  · exact solution_energy_analytic a ⟨lt_of_le_of_ne ht.1 (Ne.symm h),by linarith [ht.2]⟩ z

/-- The actual original energy derivative has the same uniform inverse-frequency bound on the positive real axis.
Use: controls differences between the true Bessel and reference spectral values in the actual GL kernel.
Article: jacobi, Proposition C.2.
Proof: use a genuine unit-radius energy Cauchy circle and the proved
actual source bound on its whole disk. The actual spectral solution is
entire, so the community Cauchy derivative is its true energy derivative. -/
theorem solution_energy_deriv_bound {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ E r:ℝ,1≤r → r^2+1≤E- jacobi.Jacobi.endpointCorrection a →
      ∀ t∈Icc (0:ℝ) (1/2),‖deriv (fun z => solution a z t) (E:ℂ)‖≤C*r^(-gamma a) := by
  -- The unit Cauchy radius is sufficient for the summable original F_k bound; no sharper derivative estimate is assumed.
  obtain ⟨C,hC,hbound⟩ := solution_energy_disk_bound ha
  refine ⟨C,hC,fun E r hr hE t ht => ?_⟩
  have hd : DifferentiableOn ℂ (fun z => solution a z t) univ :=
    fun z _ => (solution_energy_analytic_half ha ht z).differentiableAt.differentiableWithinAt
  rw [← Complex.cderiv_eq_deriv isOpen_univ hd (by norm_num : (0:ℝ)<1) (subset_univ _)]
  have hh := Complex.norm_cderiv_le (by norm_num : (0:ℝ)<1)
    (fun z hz => hbound E r hr hE z (Metric.sphere_subset_closedBall hz) t ht)
  simpa only [div_one] using hh

/-- The real-valued original reference solution, taken from its proved genuine real complex-energy value.
Use: supplies exactly the original real functions in the GL kernel and its real quadratic form.
Article: jacobi, Proposition C.2.
-/
def realSolution (a E t : ℝ) : ℝ := (solution a (E:ℂ) t).re

/-- The real reference function is exactly the genuine source solution at its actual real energy.
Use: all bounds and differential identities transfer to the actual real GL data without replacing the source function.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: the actual source spectral solution satisfies proved Schwarz reflection and is fixed at every real energy. -/
theorem realSolution_cast (a E t : ℝ) : (realSolution a E t:ℂ)=solution a (E:ℂ) t :=
  solution_real a E t

/-- The genuine original real reference solution has a uniform high-energy Lipschitz bound on every actual real segment above the prescribed shifted energy threshold.
Use: controls the actual spectral displacement term in the genuine source F_k kernel.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: the actual entire energy derivative restricts to the real source
solution, whose derivative norm is no greater than the true complex
one. The proved uniform Cauchy bound applies on the convex real
half-line containing both original energies; use the genuine mean value
inequality there. -/
theorem realSolution_energy_lipschitz {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ r:ℝ,1≤r → ∀ E F:ℝ,
      r^2+1≤E- jacobi.Jacobi.endpointCorrection a →
      r^2+1≤F- jacobi.Jacobi.endpointCorrection a → ∀ t∈Icc (0:ℝ) (1/2),
        |realSolution a F t-realSolution a E t|≤C*r^(-gamma a)*|F-E| := by
  -- Both actual source energies lie in one genuine convex derivative-control region.
  obtain ⟨C,hC,hbound⟩ := solution_energy_deriv_bound ha
  refine ⟨C,hC,fun r hr E F hE hF t ht => ?_⟩
  let D : Set ℝ := Ici (r^2+1+ jacobi.Jacobi.endpointCorrection a)
  have hderiv (x : ℝ) : HasDerivAt (fun E => realSolution a E t)
      (deriv (fun z => solution a z t) (x:ℂ)).re x :=
    (solution_energy_analytic_half ha ht (x:ℂ)).differentiableAt.hasDerivAt.real_of_complex
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
    (fun x (_ : x∈D) => (hderiv x).differentiableAt)
    (fun x (hx : x∈D) => by
      rw [(hderiv x).deriv,Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans (hbound x r hr (by change r^2+1+ jacobi.Jacobi.endpointCorrection a≤x at hx; linarith) t ht))
    (convex_Ici _) (show E∈D by change _≤E; linarith) (show F∈D by change _≤F; linarith)
  simpa only [Real.norm_eq_abs] using hh

end
end jacobi.Reference
