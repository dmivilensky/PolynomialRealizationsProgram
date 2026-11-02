import jacobi.Reference.SolutionBounds
import jacobi.Reference.SpectralScale

/-!
Article: jacobi, Proposition C.2.
The actual reference functions at both genuine source spectra have one
uniform inverse-index amplitude bound. Their genuine difference has an
additional inverse-square factor. These proved estimates are sufficient
for the original GL kernel series, without assuming a spectral-solution
asymptotic certificate or a sharper unused derivative estimate.
Use: identifies the literal source f(t,tau_k) and its original squared norm in the GL kernel.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual real-energy reference solution at the original reference spectrum is precisely its genuine Gegenbauer eigenfunction.
Use: identifies the literal source f(t,tau_k) and its original squared norm in the GL kernel.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: take real parts in the already proved genuine complex-energy reference spectral identity. -/
theorem realSolution_at_reference (a : ℝ) (k : ℕ) (t : ℝ) :
    realSolution a (eigenvalue a k) t=eigenfunction a k t := by
  simpa only [realSolution,Complex.ofReal_re] using congrArg Complex.re (solution_at_eigenvalue a k t)

/-- Both actual source spectral solutions have the uniform inverse-index bound, and their actual displacement has the extra inverse-square factor.
Use: proves the genuine source GL summands are uniformly O(k^-2) after division by the actual reference norm.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: the genuine spectra have a common increasing frequency scale.
Apply the proved original energy-disk amplitude and real-energy Lipschitz
bounds at that scale, then insert the true McMahon displacement.
Positive-base real-power multiplication gives exactly the original
index powers and fixed order-dependent constants. -/
theorem spectral_solution_bounds {a : ℝ} (ha : -1<a) :
    ∃ A B : ℝ,0<A ∧ 0<B ∧ ∀ᶠ k:ℕ in atTop,∀ t∈Icc (0:ℝ) (1/2),
      |realSolution a (jacobi.Bessel.sigma a ha k) t|≤A*(k+1:ℝ)^(-gamma a) ∧
      |realSolution a (eigenvalue a k) t|≤A*(k+1:ℝ)^(-gamma a) ∧
      |realSolution a (jacobi.Bessel.sigma a ha k) t-realSolution a (eigenvalue a k) t|≤
        B*(k+1:ℝ)^(-gamma a)/(k+1:ℝ)^2 := by
  -- Every spectral and reference estimate is already proved for the actual original objects.
  obtain ⟨C,hC,hamplitude⟩ := solution_energy_disk_bound ha
  obtain ⟨D,hD,hlipschitz⟩ := realSolution_energy_lipschitz ha
  obtain ⟨M,hM,herror⟩ := spectrum_error ha
  obtain ⟨d,hd,hscale⟩ := spectral_energy_scale ha
  refine ⟨C*d^(-gamma a),D*d^(-gamma a)*M,by positivity,by positivity,?_⟩
  filter_upwards [hscale] with k hk t ht
  have hkp : 0<(k+1:ℝ) := by positivity
  have hpow : (d*(k+1:ℝ))^(-gamma a)=d^(-gamma a)*(k+1:ℝ)^(-gamma a) :=
    Real.mul_rpow hd.le hkp.le
  have hb := hamplitude (jacobi.Bessel.sigma a ha k) (d*(k+1:ℝ)) hk.1 hk.2.2
    (jacobi.Bessel.sigma a ha k:ℂ) (Metric.mem_closedBall_self (by norm_num)) t ht
  have hr := hamplitude (eigenvalue a k) (d*(k+1:ℝ)) hk.1 hk.2.1
    (eigenvalue a k:ℂ) (Metric.mem_closedBall_self (by norm_num)) t ht
  have hb' := (Complex.abs_re_le_norm (solution a (jacobi.Bessel.sigma a ha k:ℂ) t)).trans hb
  have hr' := (Complex.abs_re_le_norm (solution a (eigenvalue a k:ℂ) t)).trans hr
  have hdiff := hlipschitz (d*(k+1:ℝ)) hk.1 (eigenvalue a k) (jacobi.Bessel.sigma a ha k)
    hk.2.1 hk.2.2 t ht
  have hm := mul_le_mul_of_nonneg_left (herror k) (show 0≤D*(d*(k+1:ℝ))^(-gamma a) by positivity)
  rw [hpow] at hb' hr' hdiff hm
  refine ⟨hb'.trans_eq (by ring),hr'.trans_eq (by ring),?_⟩
  exact (hdiff.trans hm).trans_eq (by ring)

end
end jacobi.Reference
