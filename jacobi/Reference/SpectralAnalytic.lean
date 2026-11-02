import jacobi.Reference.SpectralSeries

/-!
Article: jacobi, Appendix C.1 (selected endpoint branch).
The actual paired energy coefficients admit a summable bound on every
energy disk. Thus the original spectral solution is entire in z, including
at z=c_0alpha where choosing and differentiating a square root would fail.
Use: proves genuine normal convergence of the original reference series in the energy variable.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- On each compact energy disk the actual original energy coefficients have one positive-parameter hypergeometric majorant.
Use: proves genuine normal convergence of the original reference series in the energy variable.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: the norm square of the chosen frequency is exactly the norm of
the true shifted energy. A common disk bound therefore bounds its norm.
Use the exact polynomial/frequency coefficient identity and the already
proved uniform frequency coefficient majorant. -/
theorem energyCoefficient_bound (a : ℝ) (z0 : ℂ) :
    ∃ D : ℝ,0<D ∧ ∀ z∈Metric.ball z0 1,∀ n,
      ‖energyCoefficient a n z‖≤
        ‖ordinaryHypergeometricCoefficient (D:ℂ) (D:ℂ) ((gamma a:ℂ)+1/2) n‖ := by
  -- No continuity of the arbitrary square-root branch is needed; only its genuine square is used.
  let R := ‖z0‖+|jacobi.Jacobi.endpointCorrection a|+2
  have hR : 0<R := by dsimp [R]; positivity
  let D := |gamma a|+R/Real.pi+1
  refine ⟨D,by dsimp [D]; positivity,fun z hz n => ?_⟩
  let omega := Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))
  have hs : ‖omega‖^2=‖z-(jacobi.Jacobi.endpointCorrection a:ℂ)‖ := by
    rw [← norm_pow]
    exact congrArg norm (frequency_square _)
  have hz' : ‖z-z0‖<1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hz
  have hzn : ‖z‖≤‖z0‖+1 := by
    have hh := norm_add_le (z-z0) z0
    rw [sub_add_cancel] at hh
    linarith
  have he : ‖z-(jacobi.Jacobi.endpointCorrection a:ℂ)‖≤R-1 := by
    have hh := norm_sub_le z (jacobi.Jacobi.endpointCorrection a:ℂ)
    rw [Complex.norm_real,Real.norm_eq_abs] at hh
    dsimp [R]
    linarith
  have homega : ‖omega‖≤R := by nlinarith [norm_nonneg omega,sq_nonneg (R-1)]
  rw [energyCoefficient_eq_frequency a (frequency_square _) n]
  exact frequencyCoefficient_norm_bound a hR.le homega n

/-- The actual reference hypergeometric core as a square-root-free function of its original energy and spatial coordinate.
Use: supplies the genuine entire energy dependence and joint continuity of the original source solution.
Article: jacobi, Appendix C.2 (exact parity splitting).
-/
def energyCore (a : ℝ) (z x : ℂ) : ℂ := ∑' n,energyCoefficient a n z*x^n

/-- The actual reference spectral core is entire in its original complex energy at every spatial argument inside its disk.
Use: gives the original source's true entire energy function without an auxiliary analyticity hypothesis.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: on an energy disk the actual polynomial coefficients have the
proved convergent 2F1 majorant. The community holomorphic-series theorem
applies termwise to the actual energy polynomials, including at the
frequency branch point z=c_0alpha. -/
theorem energyCore_analytic (a : ℝ) {x : ℂ} (hx : ‖x‖<1) (z0 : ℂ) :
    AnalyticAt ℂ (fun z => energyCore a z x) z0 := by
  -- The normal series consists of actual energy polynomials, not analytically continued root expressions.
  obtain ⟨D,hD,hbound⟩ := energyCoefficient_bound a z0
  let M := fun n => ‖ordinaryHypergeometricCoefficient (D:ℂ) (D:ℂ) ((gamma a:ℂ)+1/2) n*x^n‖
  have hM : Summable M := Hypergeometric.summable_norm hx
  have hd := Complex.differentiableOn_tsum_of_summable_norm hM
    (F := fun n z => energyCoefficient a n z*x^n)
    (fun n z _ => ((energyCoefficient_analytic a n z).mul analyticAt_const).differentiableAt.differentiableWithinAt)
    Metric.isOpen_ball (fun n z hz => by
      change ‖energyCoefficient a n z*x^n‖≤
        ‖ordinaryHypergeometricCoefficient (D:ℂ) (D:ℂ) ((gamma a:ℂ)+1/2) n*x^n‖
      rw [norm_mul,norm_mul]
      exact mul_le_mul_of_nonneg_right (hbound z hz n) (norm_nonneg _))
  exact hd.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))

/-- The genuine reference spectral solution is entire in its actual energy for every original interior spatial point.
Use: supplies the original entire functions appearing in GL positivity, midpoint characteristic identities and transformed solutions.
Article: jacobi, Lemma C.1.
Proof: the original reference definition equals the actual polynomial-coefficient energy series; its sine-power prefactor is energy-independent. -/
theorem solution_energy_analytic (a : ℝ) {t : ℝ} (ht : t∈Ioo 0 1) (z : ℂ) :
    AnalyticAt ℂ (fun z => solution a z t) z := by
  have he : (fun z => solution a z t)=(fun z => (weight a t:ℂ)*energyCore a z (coordinate t:ℂ)) :=
    funext fun z => solution_eq_energy_series a z t
  rw [he]
  exact analyticAt_const.mul (energyCore_analytic a (coordinate_norm_lt_one ht) z)

end
end jacobi.Reference
