import jacobi.GelfandLevitan.TransformedSolution
import jacobi.Reference.FrequencyStrip

/-!
Article: jacobi, Proposition 2.2.
The actual constructed transformation preserves the reference minimum
envelope on every fixed complex-frequency strip. Its genuine inverse
rows have the required physical support and one common L2 bound.
Thus the original u satisfies the endpoint and inverse-frequency bound
used to control the source spectral profiles, without a new estimate
assumed for u or for its kernel.
Use: the already proved original reference frequency envelopes are transferred to the actual constructed u, with no separate transformed-solution estimate as a premise of the source theorem.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace

/-- A true prefix bound for the reference solution bounds its actual GL transform by the same scale times one plus the genuine inverse-row norm.
Use: the already proved original reference frequency envelopes are transferred to the actual constructed u, with no separate transformed-solution estimate as a premise of the source theorem.
Article: jacobi, Proposition C.4.
Proof: outside the physical prefix the actual inverse row is zero.
On that prefix the reference factor is bounded by the prescribed scale.
The genuine coefficient integral is therefore bounded by that scale
times the original L1 norm, which is at most its true L2 norm.
Add the actual reference value at the physical endpoint. -/
theorem transformedSolution_norm_le (a : ℝ) (ha : -1<a) (t : HalfInterval) (z : ℂ)
    {M : ℝ} (hM : 0≤M) (hf : ∀ r∈Icc (0:ℝ) (t:ℝ),‖solution a z r‖≤M) :
    ‖transformedSolution a ha t z‖≤M*(1+‖solutionRow a ha t‖) := by
  -- The moving boundary is controlled by the proved support of the original inverse row.
  let v : Space := (solutionRow a ha t:Space)
  have hi : ‖coefficientFunctional v (halfSolution a ha z)‖≤‖v‖*M := by
    change ‖∫ r:Interval,(v r:ℂ)*halfSolution a ha z r‖≤_
    have hh := norm_integral_le_of_norm_le (f := fun r:Interval => (v r:ℂ)*halfSolution a ha z r)
      ((space_integrable v).norm.mul_const M) (by
        filter_upwards [(mem_cutoffSubspace_iff _ _).mp (solutionRow_mem a ha t)] with r hr
        rw [norm_mul,Complex.norm_real,halfSolution_apply]
        by_cases hp : (r:ℝ)≤(t:ℝ)
        · have hprefix : halfTime r∈Icc (0:ℝ) (t:ℝ) :=
            ⟨(halfTime_mem r).1,(min_le_left (r:ℝ) (1/2)).trans hp⟩
          exact mul_le_mul_of_nonneg_left (hf _ hprefix) (norm_nonneg _)
        · have hv : v r=0 := hr (lt_of_not_ge hp)
          rw [hv,norm_zero,zero_mul,zero_mul])
    rw [integral_mul_const] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (space_L1_le_norm v) hM)
  rw [transformedSolution_reference_form]
  calc
    _ ≤ ‖solution a z (t:ℝ)‖+‖coefficientFunctional v (halfSolution a ha z)‖ := norm_add_le _ _
    _ ≤ M+‖v‖*M := add_le_add (hf _ ⟨t.property.1,le_rfl⟩) hi
    _ = _ := by change M+‖solutionRow a ha t‖*M=_; ring

/-- The actual constructed transformed solution has the full original endpoint/inverse-frequency minimum bound on every fixed complex-frequency strip.
Use: controls the original perturbed spectral profiles and the uniform convergence of the persymmetric profile series, using the proved actual reference estimates and GL solution only.
Article: jacobi, Proposition 2.2.
Proof: the original reference strip estimate on every physical prefix
is bounded by its endpoint minimum, since the positive endpoint power
is monotone. The true GL norm estimate and the proved common inverse-row
bound multiply this original scale by one fixed positive constant. -/
theorem transformedSolution_strip_bound (a : ℝ) (ha : -1<a) (b : ℝ) :
    ∃ C:ℝ,0<C ∧ ∀ omega:ℂ,omega≠0 → |omega.im|≤b → ∀ t:HalfInterval,
      ‖transformedSolution a ha t ((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2)‖≤
        C*min ((t:ℝ)^(gamma a)) (‖omega‖^(-gamma a)) := by
  -- All constants come from the actual source reference wave and the proved original inverse solution, uniformly in the physical endpoint.
  obtain ⟨A,hA,hReference⟩ := wave_strip_bound ha b
  obtain ⟨B,hB,hRows⟩ := solutionRow_bounded a ha
  refine ⟨A*(1+B),by positivity,fun omega hne him t => ?_⟩
  let m := min ((t:ℝ)^(gamma a)) (‖omega‖^(-gamma a))
  have hm : 0≤m := le_min (Real.rpow_nonneg t.property.1 _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hg : 0≤gamma a := by linarith [(parameters ha).1]
  have hf (r : ℝ) (hr : r∈Icc (0:ℝ) (t:ℝ)) :
      ‖solution a ((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2) r‖≤A*m := by
    rw [solution_eq_wave a (omega := omega) (by ring)]
    have hh := hReference omega hne him r ⟨hr.1,hr.2.trans t.property.2⟩
    exact hh.trans (mul_le_mul_of_nonneg_left
      (min_le_min (Real.rpow_le_rpow hr.1 hr.2 hg) le_rfl) hA.le)
  calc
    _ ≤ (A*m)*(1+‖solutionRow a ha t‖) :=
      transformedSolution_norm_le a ha t _ (mul_nonneg hA.le hm) hf
    _ ≤ (A*m)*(1+B) := mul_le_mul_of_nonneg_left (add_le_add le_rfl (hRows t)) (mul_nonneg hA.le hm)
    _ = _ := by dsimp [m]; ring

end
end jacobi.GelfandLevitan
