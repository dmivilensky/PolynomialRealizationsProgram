import jacobi.GelfandLevitan.TransformedBounds
import jacobi.Reference.EndpointUniform

/-!
Article: jacobi, Proposition C.4.
The literal GL integral is O(t^(gamma+1)) because K is bounded and its
physical integration interval has length t. Thus the actual transformed
function has u=t^gamma*(1+O(t)), including gamma<1/2 where mere endpoint
vanishing would fail to identify the source's selected branch.
Use: obtains the extra factor t in the actual transformation correction and subsequent endpoint and kernel estimates.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory Filter jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] transformedSolution solution transformationKernel

/-- The true physical GL prefix has exactly its original Lebesgue length.
Use: obtains the extra factor t in the actual transformation correction and subsequent endpoint and kernel estimates.
Article: jacobi, Proposition C.4.
Source: Lebesgue interval measure and mathlib's subtype measure.
Proof: the injective measurable coordinate sends the actual prefix
exactly onto [0,t]. Its subtype measure is therefore the original real
interval measure, with no change of normalization. -/
theorem prefix_volume (t : HalfInterval) :
    (volume : Measure Interval) (prefixSet (t:ℝ))=ENNReal.ofReal (t:ℝ) := by
  -- Identify the actual coordinate image before evaluating its Lebesgue measure.
  have hm : MeasurableEmbedding (Subtype.val : Interval → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  rw [Measure.Subtype.volume_def,hm.comap_apply]
  have he : Subtype.val '' prefixSet (t:ℝ)=Icc (0:ℝ) (t:ℝ) := by
    ext x
    constructor
    · rintro ⟨s,hs,rfl⟩
      exact ⟨s.property.1,hs⟩
    · intro hx
      exact ⟨⟨x,hx.1,hx.2.trans (t.property.2.trans (by norm_num))⟩,hx.2,rfl⟩
  rw [he,Real.volume_Icc,sub_zero]

/-- The actual GL correction gains one full spatial power relative to the selected singular reference branch.
Use: proves transformedSolution_selected_branch and prevents confusing the two endpoint branches when gamma<1/2.
Article: jacobi, Proposition C.4.
Proof: the constructed actual K has one uniform bound. On [0,t] the
genuine reference envelope is at most C_z*t^gamma, so the literal
transformation integral has norm at most their product times its
proved original interval length t. -/
theorem transformedSolution_endpoint_correction (a : ℝ) (ha : -1<a) (z : ℂ) :
    ∃ C : ℝ,0<C ∧ ∀ t : HalfInterval,
      ‖transformedSolution a ha t z-solution a z (t:ℝ)‖≤C*(t:ℝ)^(gamma a)*(t:ℝ) := by
  -- The extra power comes from the true integration measure, rather than an assumed differentiability of K.
  obtain ⟨A,hA,hf⟩ := wave_global_endpoint_bound ha
  obtain ⟨B,hB,hK⟩ := transformationKernel_bounded a ha
  let w := Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))
  let D := A*Real.exp (|w.im|/2)
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨B*D,by positivity,fun t => ?_⟩
  have hbound (r : Interval) (hr : r∈prefixSet (t:ℝ)) :
      ‖(transformationKernel a ha t (halfClamp r):ℂ)*solution a z (halfTime r)‖≤
        B*D*(t:ℝ)^(gamma a) := by
    have hp : halfTime r≤(t:ℝ) := (min_le_left _ _).trans hr
    have hs := hf w (halfTime r) (halfTime_mem r)
    rw [← solution_eq_wave a (frequency_square _) (halfTime r)] at hs
    have hpow := Real.rpow_le_rpow (halfTime_mem r).1 hp
      (show 0≤gamma a by linarith [(parameters ha).1])
    have hExp : Real.exp (halfTime r*|w.im|)≤Real.exp (|w.im|/2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [(halfTime_mem r).2,abs_nonneg w.im]
    have hval : ‖solution a z (halfTime r)‖≤D*(t:ℝ)^(gamma a) := by
      calc
        _ ≤ A*(halfTime r)^(gamma a)*Real.exp (halfTime r*|w.im|) := hs
        _ ≤ A*(t:ℝ)^(gamma a)*Real.exp (|w.im|/2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow hA.le) hExp
            (Real.exp_pos _).le (mul_nonneg hA.le (Real.rpow_nonneg t.property.1 _))
        _ = _ := by dsimp [D]; ring
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact (mul_le_mul (hK t (halfClamp r)) hval (norm_nonneg _) hB.le).trans_eq (by ring)
  rw [transformedSolution_integral,add_sub_cancel_left]
  have hh := norm_setIntegral_le_of_norm_le_const
    (measure_lt_top (volume : Measure Interval) (prefixSet (t:ℝ))) hbound
  rw [Measure.real,prefix_volume,ENNReal.toReal_ofReal t.property.1] at hh
  exact hh

/-- The constructed transformed solution has exactly the source's selected normalized endpoint branch with its full linear relative remainder.
Use: supplies the endpoint assertion in Proposition C.2, including the limit-circle range gamma<1/2, for the same actual u used by all spectral profiles.
Article: jacobi, Proposition C.4.
Proof: the true reference relative error is quadratic. Divide the
actual O(t^(gamma+1)) GL correction by the genuinely nonzero positive
endpoint power. Their sum is O(t), since t<=1/2. Every filter here is
the actual physical half interval approaching its true zero endpoint. -/
theorem transformedSolution_selected_branch (a : ℝ) (ha : -1<a) (z : ℂ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ t : HalfInterval in 𝓝[>] halfZero,
      ‖transformedSolution a ha t z/(((t:ℝ)^(gamma a):ℝ):ℂ)-1‖≤C*(t:ℝ) := by
  -- Move the established reference endpoint limit to the genuine physical half-interval filter.
  obtain ⟨A,hA,hcorr⟩ := transformedSolution_endpoint_correction a ha z
  obtain ⟨B,hB,href⟩ := solution_uniform_relative_error a z
  have htend : Tendsto (fun t : HalfInterval => (t:ℝ)) (𝓝[>] halfZero) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht
  refine ⟨A+B,by positivity,?_⟩
  filter_upwards [htend.eventually href,self_mem_nhdsWithin] with t ht htpos
  have htp : 0<(t:ℝ) := htpos
  have hp : 0<(t:ℝ)^(gamma a) := Real.rpow_pos_of_pos htp _
  have hdiff : ‖(transformedSolution a ha t z-solution a z (t:ℝ))/
      (((t:ℝ)^(gamma a):ℝ):ℂ)‖≤A*(t:ℝ) := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
    apply (div_le_iff₀ hp).mpr
    exact (hcorr t).trans_eq (by ring)
  have he : transformedSolution a ha t z/(((t:ℝ)^(gamma a):ℝ):ℂ)-1=
      (transformedSolution a ha t z-solution a z (t:ℝ))/(((t:ℝ)^(gamma a):ℝ):ℂ)+
        (solution a z (t:ℝ)/(((t:ℝ)^(gamma a):ℝ):ℂ)-1) := by ring
  rw [he]
  have hquad := ht z (Metric.mem_closedBall_self (by norm_num : (0:ℝ)≤1/4))
  have htone : (t:ℝ)^2≤(t:ℝ) := by nlinarith [t.property.2]
  exact (norm_add_le _ _).trans ((add_le_add hdiff hquad).trans (by nlinarith))

end
end jacobi.GelfandLevitan
