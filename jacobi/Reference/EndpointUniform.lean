import jacobi.Reference.CoreBounds
import jacobi.Reference.SolutionFactor

/-!
Article: jacobi, Proposition C.4.
The actual selected branch has a quadratic relative remainder locally
uniformly in energy. Differences of two original reference solutions have
the extra factor norm(z-w) and the exact source endpoint power gamma+2.
These follow from the genuine energy Cauchy bounds and the actual
regular-singular factorization, not from assumed Frobenius data.
Use: transfers the compact-uniform spectral core bounds to the selected original endpoint branch.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex Filter Asymptotics
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual arbitrary-energy regular endpoint factor equals the true degree-zero reference regular weight times the genuine energy core.
Use: transfers the compact-uniform spectral core bounds to the selected original endpoint branch.
Article: jacobi, Lemma C.1.
Proof: the actual degree-zero normalized Jacobi polynomial is one; both remaining factors are exactly the original definitions. -/
theorem solutionFactor_eq_core (a : ℝ) (z : ℂ) (t : ℝ) :
    solutionFactor a z t=(regularFactor a 0 t:ℂ)*energyCore a z (coordinate t:ℂ) := by
  have hp : jacobi.Jacobi.shiftedPolynomial (jacobiIndex a) (jacobiIndex a) 0=1 := by
    simp [jacobi.Jacobi.shiftedPolynomial,jacobi.Jacobi.coefficient_zero]
  rw [energyCore_eq_waveCore]
  simp only [solutionFactor,regularFactor,jacobi.Jacobi.angular,hp,Polynomial.eval_one,mul_one]

/-- The original cosine coordinate is quadratically small at its actual singular endpoint, with a global explicit constant.
Use: converts the actual core's spatially linear remainder into the source's quadratic spatial endpoint order.
Article: jacobi, Proposition C.4.
Proof: apply the community global quadratic cosine lower bound to pi*t and use the literal shifted cosine coordinate. -/
theorem coordinate_quadratic (t : ℝ) : ‖(coordinate t:ℂ)‖≤(Real.pi^2/4)*t^2 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (coordinate_properties.2.2 t).1]
  have hh := Real.one_sub_sq_div_two_le_cos (x := Real.pi*t)
  dsimp [coordinate]
  nlinarith

/-- Near zero the actual degree-zero regular reference weight is bounded by two and its actual spatial coordinate stays in the half-radius disk.
Use: gives common endpoint neighborhoods for all energies in the genuine uniform reference estimates.
Article: jacobi, Proposition C.4.
Proof: both original functions are continuous at zero, with respective values one and zero. Apply the genuine open-neighborhood continuity criterion. -/
theorem regular_endpoint_neighborhood (a : ℝ) :
    ∀ᶠ t:ℝ in 𝓝 0,‖(regularFactor a 0 t:ℂ)‖≤2 ∧ ‖(coordinate t:ℂ)‖≤1/2 := by
  -- Take the same genuine neighborhood for both continuous original endpoint factors.
  have hg : ContinuousAt (fun t:ℝ => (coordinate t:ℂ)) 0 := (Complex.continuous_ofReal.comp
    (continuous_iff_continuousAt.mpr (fun t => (coordinate_hasDerivAt t).continuousAt))).continuousAt
  have hr : ContinuousAt (fun t:ℝ => (regularFactor a 0 t:ℂ)) 0 := Complex.continuous_ofReal.continuousAt.comp_of_eq
    (regularFactor_analytic a 0).continuousAt rfl
  have h1 : ∀ᶠ t:ℝ in 𝓝 0,‖(regularFactor a 0 t:ℂ)‖<2 := by
    apply hr.norm.eventually (Iio_mem_nhds _)
    change ‖(regularFactor a 0 (0:ℝ):ℂ)‖<2
    rw [regularFactor_zero,Complex.ofReal_one,norm_one]
    norm_num
  have h2 : ∀ᶠ t:ℝ in 𝓝 0,‖(coordinate t:ℂ)‖<1/2 := by
    apply hg.norm.eventually (Iio_mem_nhds _)
    change ‖(coordinate (0:ℝ):ℂ)‖<1/2
    rw [coordinate_properties.1,Complex.ofReal_zero,norm_zero]
    norm_num
  filter_upwards [h1,h2] with t ht1 ht2
  exact ⟨ht1.le,ht2.le⟩

/-- The actual regular reference endpoint factors have a compact-uniform energy Lipschitz bound with the genuine quadratic spatial order.
Use: proves the source energy difference estimate after restoring the selected singular endpoint power.
Article: jacobi, Proposition C.4.
Proof: factor out the actual degree-zero regular weight, bounded by
two near zero. Apply the proved genuine core energy Lipschitz bound and
the explicit quadratic cosine-coordinate estimate. -/
theorem solutionFactor_uniform_lipschitz (a : ℝ) (z0 : ℂ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ t:ℝ in 𝓝 0,∀ z∈Metric.closedBall z0 (1/4),
      ∀ w∈Metric.closedBall z0 (1/4),
        ‖solutionFactor a w t-solutionFactor a z t‖≤C*t^2*‖w-z‖ := by
  -- Both true energies vary in the same fixed disk and use the same actual endpoint neighborhood.
  obtain ⟨B,hB,hbound⟩ := energyCore_energy_lipschitz a z0
  refine ⟨2*B*(Real.pi^2/4),by positivity,?_⟩
  filter_upwards [regular_endpoint_neighborhood a] with t ht z hz w hw
  rw [solutionFactor_eq_core,solutionFactor_eq_core,← mul_sub,norm_mul]
  have hm := mul_le_mul ht.1 (hbound (coordinate t:ℂ) ht.2 z hz w hw)
    (norm_nonneg _) (by norm_num : (0:ℝ)≤2)
  have hq := mul_le_mul_of_nonneg_right (coordinate_quadratic t)
    (show 0≤2*B*‖w-z‖ by positivity)
  nlinarith [hm,hq]

/-- The actual selected regular reference factors have a quadratic endpoint remainder locally uniformly in the original complex energy.
Use: gives the full compact-local source endpoint normalization f(t,z)=t^gamma*(1+O(t^2)).
Article: jacobi, Lemma C.1.
Proof: the true regular factor at the central energy has a proved
quadratic analytic remainder. Its difference from any energy in the
quarter-radius disk has the proved quadratic energy Lipschitz bound.
Add the two actual remainders and bound the true energy displacement. -/
theorem solutionFactor_uniform_quadratic (a : ℝ) (z0 : ℂ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ t:ℝ in 𝓝 0,∀ z∈Metric.closedBall z0 (1/4),
      ‖solutionFactor a z t-1‖≤C*t^2 := by
  -- A single actual endpoint expansion, together with the proved genuine difference estimate, makes the bound uniform in energy.
  obtain ⟨A,hA,hbase⟩ := isBigO_iff'.mp (solutionFactor_quadratic a z0)
  obtain ⟨B,hB,hbound⟩ := solutionFactor_uniform_lipschitz a z0
  refine ⟨A+B/4,by positivity,?_⟩
  filter_upwards [hbase,hbound] with t ht hb z hz
  have hz' : ‖z-z0‖≤1/4 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  have hdiff := hb z0 (Metric.mem_closedBall_self (by norm_num)) z hz
  have hm := mul_le_mul_of_nonneg_left hz' (show 0≤B*t^2 by positivity)
  have hh := norm_add_le (solutionFactor a z t-solutionFactor a z0 t) (solutionFactor a z0 t-1)
  rw [sub_add_sub_cancel] at hh
  simp only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg t)] at ht
  nlinarith [hh,ht,hdiff,hm]

/-- The genuine original arbitrary-energy reference solutions satisfy the source's locally uniform endpoint energy difference estimate.
Use: controls the actual singular boundary terms and differences of the original spectral data in the GL construction.
Article: jacobi, Proposition C.4.
Proof: restore the true selected positive-axis factor t^gamma in both
original reference functions. The proved uniform regular-factor
Lipschitz estimate supplies t^2. Combine the two genuine positive-base
real powers to get exactly the printed exponent gamma+2. -/
theorem solution_uniform_energy_difference (a : ℝ) (z0 : ℂ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ t:ℝ in 𝓝[>] 0,∀ z∈Metric.closedBall z0 (1/4),
      ∀ w∈Metric.closedBall z0 (1/4),
        ‖solution a w t-solution a z t‖≤C*t^(gamma a+2)*‖w-z‖ := by
  -- The exact actual endpoint power is used, including when gamma<1/2.
  obtain ⟨C,hC,hbound⟩ := solutionFactor_uniform_lipschitz a z0
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound.filter_mono nhdsWithin_le_nhds,
    Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht htpos z hz w hw
  rw [solution_factor a w htpos,solution_factor a z htpos,← mul_sub,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos htpos.1 _)]
  have hh := mul_le_mul_of_nonneg_left (ht z hz w hw) (Real.rpow_pos_of_pos htpos.1 (gamma a)).le
  rw [Real.rpow_add htpos.1,Real.rpow_two]
  nlinarith [hh]


/-- The genuine source reference solutions have their printed quadratic relative endpoint expansion locally uniformly in complex energy.
Use: supplies the original selected endpoint normalization in the GL construction, with the full local uniformity required in the article.
Article: jacobi, Lemma C.1.
Proof: cancel the true nonzero positive-axis endpoint power in the
actual reference factorization. The proved uniform quadratic regular
factor bound then gives exactly the original relative remainder. -/
theorem solution_uniform_relative_error (a : ℝ) (z0 : ℂ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ t:ℝ in 𝓝[>] 0,∀ z∈Metric.closedBall z0 (1/4),
      ‖solution a z t/((t^(gamma a):ℝ):ℂ)-1‖≤C*t^2 := by
  -- The singular outer power is cancelled only where it is genuinely nonzero on the original positive axis.
  obtain ⟨C,hC,hbound⟩ := solutionFactor_uniform_quadratic a z0
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound.filter_mono nhdsWithin_le_nhds,
    Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with t ht htpos z hz
  rw [solution_factor a z htpos,mul_div_cancel_left₀ _ (show ((t^(gamma a):ℝ):ℂ)≠0 by
    exact_mod_cast (Real.rpow_pos_of_pos htpos.1 (gamma a)).ne')]
  exact ht z hz

end
end jacobi.Reference
