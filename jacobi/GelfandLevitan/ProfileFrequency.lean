import jacobi.GelfandLevitan.NegativePointBounds
import jacobi.Reference.BesselFrequency

/-!
Article: jacobi, Proposition 2.2.
At each positive half-interval point, the actual transformed solution
is an entire frequency function of type at most one half. The original
Bessel frequencies cannot all be its zeros: Jensen uniqueness would
contradict its proved strict positivity at sufficiently negative energy.
Use: transformed_spectral_nonvanishing applies the already proved Jensen uniqueness theorem to the actual pointwise GL solution.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The genuine transformed solution, expressed in the source frequency coordinate, satisfies the required entire-function growth bound.
Use: transformed_spectral_nonvanishing applies the already proved Jensen uniqueness theorem to the actual pointwise GL solution.
Article: jacobi, Proposition 2.2.
Proof: on each original physical prefix the reference endpoint power
is at most one and its exponential is at most exp(|omega|/2). The
genuine bounded inverse GL row preserves that bound up to one constant. -/
theorem transformed_frequency_growth (a:ℝ) (ha:-1<a) (t:HalfInterval) :
    ∃ C:ℝ,0<C ∧ ∀ w:ℂ,
      ‖transformedSolution a ha t ((jacobi.Jacobi.endpointCorrection a:ℂ)+w^2)‖≤
        C*Real.exp (‖w‖/2) := by
  -- The all-frequency reference estimate includes the original frequency zero.
  obtain ⟨A,hA,hbound⟩ := wave_global_endpoint_bound ha
  refine ⟨A*(1+‖solutionRow a ha t‖),by positivity,fun w=>?_⟩
  have hp (r:ℝ) (hr:r∈Icc (0:ℝ) (t:ℝ)) :
      ‖solution a ((jacobi.Jacobi.endpointCorrection a:ℂ)+w^2) r‖≤A*Real.exp (‖w‖/2) := by
    rw [solution_eq_wave a (omega:=w) (by ring)]
    have hs := hbound w r ⟨hr.1,hr.2.trans t.property.2⟩
    have hpow : r^(gamma a)≤1 := Real.rpow_le_one hr.1
      (hr.2.trans (t.property.2.trans (by norm_num))) (by linarith [(parameters ha).1])
    have he : r*|w.im|≤‖w‖/2 := by
      have hm := mul_le_mul (hr.2.trans t.property.2) (Complex.abs_im_le_norm w)
        (abs_nonneg w.im) (by norm_num : (0:ℝ)≤1/2)
      linarith
    calc
      _ ≤ A*r^(gamma a)*Real.exp (r*|w.im|) := hs
      _ ≤ A*Real.exp (‖w‖/2) := by
        have h := mul_le_mul (mul_le_of_le_one_right hA.le hpow)
          (Real.exp_le_exp.mpr he) (Real.exp_pos _).le hA.le
        exact h
  exact (transformedSolution_norm_le a ha t _ (by positivity) hp).trans_eq (by ring)

/-- At every positive physical point at least one original target spectral solution is nonzero.
Use: persymmetricProfile_pos extracts a strictly positive term from the unchanged positive source profile series.
Article: jacobi, Proposition 2.2.
Source: Levin, Distribution of Zeros of Entire Functions, Jensen uniqueness, proved in Complex.EntireUniqueness.
Proof: simultaneous zeros give both signs of every genuine shifted
Bessel frequency as zeros of the actual entire transformed function.
Its proved half-interval exponential type forces it to be zero. Its
strictly positive value at a sufficiently negative energy contradicts this. -/
theorem transformed_spectral_nonvanishing (a:ℝ) (ha:-1<a)
    (t:HalfInterval) (ht:0<(t:ℝ)) :
    ∃ k:ℕ,transformedSolution a ha t (jacobi.Bessel.sigma a ha k:ℂ)≠0 := by
  -- The uniqueness set is the true exhaustive Bessel zero sequence, with its actual source energy shift.
  by_contra hn
  push Not at hn
  let f := fun w:ℂ=>transformedSolution a ha t ((jacobi.Jacobi.endpointCorrection a:ℂ)+w^2)
  have hf (w:ℂ) : AnalyticAt ℂ f w :=
    (transformedSolution_analytic a ha t _).comp (analyticAt_const.add (analyticAt_id.pow 2))
  have hz (k:ℕ) : f (besselFrequency a ha k:ℂ)=0 ∧ f (-(besselFrequency a ha k:ℂ))=0 := by
    have he : (jacobi.Jacobi.endpointCorrection a:ℂ)+(besselFrequency a ha k:ℂ)^2=
        (jacobi.Bessel.sigma a ha k:ℂ) := by
      have hs : (jacobi.Jacobi.endpointCorrection a)+(besselFrequency a ha k)^2=
          jacobi.Bessel.sigma a ha k := by rw [besselFrequency_sq ha]; ring
      exact_mod_cast hs
    dsimp only [f]
    simp only [neg_sq,he,hn k,and_self]
  have hzero := bessel_entire_uniqueness ha hf hz (transformed_frequency_growth a ha t)
  obtain ⟨y,hy⟩ := (transformed_negative_eventually_pos a ha t ht).exists
  have he : (jacobi.Jacobi.endpointCorrection a:ℂ)+(Complex.I*(y:ℂ))^2=
      ((jacobi.Jacobi.endpointCorrection a-y^2:ℝ):ℂ) := by
    push_cast
    rw [mul_pow,Complex.I_sq]
    ring
  have hh := congrFun hzero (Complex.I*(y:ℂ))
  change transformedSolution a ha t ((jacobi.Jacobi.endpointCorrection a:ℂ)+
    (Complex.I*(y:ℂ))^2)=0 at hh
  rw [he] at hh
  simp only [hh,Complex.zero_re,lt_self_iff_false] at hy

end
end jacobi.GelfandLevitan
