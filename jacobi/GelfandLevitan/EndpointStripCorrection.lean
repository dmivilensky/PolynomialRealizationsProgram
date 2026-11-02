import jacobi.GelfandLevitan.SelectedEndpoint

/-!
Article: jacobi, Proposition C.4.
Use: the spectral endpoint comparison proves the transformed-profile minus reference-Green diagonal is o(t), as required by Proposition C.4.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] transformedSolution solution transformationKernel

/-- The actual GL correction retains both its full spatial factor t and the genuine frequency-strip minimum at every original physical point.
Use: the spectral endpoint comparison proves the transformed-profile minus reference-Green diagonal is o(t), as required by Proposition C.4.
Article: jacobi, Proposition C.4.
Proof: bound the actual K uniformly and the original reference solution by its strip minimum on the genuine prefix. The exact prefix measure is t, giving the additional factor without losing the frequency envelope. -/
theorem transformedSolution_strip_correction (a : ℝ) (ha : -1<a) (b : ℝ) :
    ∃ C : ℝ,0<C ∧ ∀ omega : ℂ,omega≠0 → |omega.im|≤b → ∀ t : HalfInterval,
      ‖transformedSolution a ha t ((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2)-
        solution a ((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2) (t:ℝ)‖≤
          C*(t:ℝ)*min ((t:ℝ)^(gamma a)) (‖omega‖^(-gamma a)) := by
  -- The integration interval is the original physical prefix, not a unit interval with its length suppressed.
  obtain ⟨A,hA,hf⟩ := wave_strip_bound ha b
  obtain ⟨B,hB,hK⟩ := transformationKernel_bounded a ha
  refine ⟨B*A,by positivity,fun omega hne him t => ?_⟩
  have hbound (r : Interval) (hr : r∈prefixSet (t:ℝ)) :
      ‖(transformationKernel a ha t (halfClamp r):ℂ)*
        solution a ((jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2) (halfTime r)‖≤
          B*A*min ((t:ℝ)^(gamma a)) (‖omega‖^(-gamma a)) := by
    have hp : halfTime r≤(t:ℝ) := (min_le_left _ _).trans hr
    have hs := hf omega hne him (halfTime r) (halfTime_mem r)
    rw [← solution_eq_wave a (z := (jacobi.Jacobi.endpointCorrection a:ℂ)+omega^2) (omega := omega) (by ring)] at hs
    have hpow := Real.rpow_le_rpow (halfTime_mem r).1 hp
      (show 0≤gamma a by linarith [(parameters ha).1])
    have hval := hs.trans (mul_le_mul_of_nonneg_left (min_le_min hpow le_rfl) hA.le)
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul (hK t (halfClamp r)) hval (norm_nonneg _) hB.le).trans_eq (by ring)
  rw [transformedSolution_integral,add_sub_cancel_left]
  have hh := norm_setIntegral_le_of_norm_le_const
    (measure_lt_top (volume : Measure Interval) (prefixSet (t:ℝ))) hbound
  rw [Measure.real,prefix_volume,ENNReal.toReal_ofReal t.property.1] at hh
  exact hh.trans_eq (by ring)

end
end jacobi.GelfandLevitan
