import jacobi.Rearrangement.RegularOrbit
import jacobi.Variational.Tails

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
A radial test maximizer in the actual compact polarization orbit is even and
nonincreasing at positive radii. The key strictness argument integrates a
continuous nonnegative reflected-pair gain, which is positive whenever an
incorrectly ordered pair survives. No symmetry or rearrangement existence is
assumed in the maximizing argument.
Source: the strict radial test functional proof of convergence of polarizations.
Use: turns a pointwise value inversion into strict improvement of the maximizing functional.
-/
namespace jacobi.Rearrangement
noncomputable section
open Set Real MeasureTheory Filter
open scoped NNReal Topology BoundedContinuousFunction
set_option backward.isDefEq.respectTransparency false

/-- Change in the radial integrand summed over a reflected pair.
Use: turns a pointwise value inversion into strict improvement of the maximizing functional.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
-/
def radialPairGain (f : ℝ →ᵇ ℝ) (a x : ℝ) : ℝ :=
  exp (-|x|)*polarize a f x+exp (-|reflect a x|)*polarize a f (reflect a x)-
    (exp (-|x|)*f x+exp (-|reflect a x|)*f (reflect a x))

/-- The pair gain is unchanged when the pair's representative is reflected.
Use: proves gain nonnegativity on the entire real line from the preferred half-line.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: double reflection is the identity and the two summands commute. -/
theorem radialPairGain_reflect (f : ℝ →ᵇ ℝ) (a x : ℝ) :
    radialPairGain f a (reflect a x)=radialPairGain f a x := by
  simp only [radialPairGain,reflect_reflect]
  ring

/-- On the preferred half-line the gain factors as weight difference times value correction.
Use: both nonnegativity and strict positivity follow from the same literal factorization.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: substitute the sorted pair and use max+min equal to the original pair sum. -/
theorem radialPairGain_left (f : ℝ →ᵇ ℝ) (a : ℝ) {x : ℝ} (hx : x ≤ a) :
    radialPairGain f a x=(exp (-|x|)-exp (-|reflect a x|))*
      (max (f x) (f (reflect a x))-f x) := by
  rw [radialPairGain,(polarize_left_pair a f hx).1,(polarize_left_pair a f hx).2]
  rcases le_total (f x) (f (reflect a x)) with h | h
  · rw [max_eq_right h,min_eq_left h]; ring
  · rw [max_eq_left h,min_eq_right h]; ring

/-- Centered polarization never decreases the radial pair integral.
Use: the strict improvement argument has no cancellation between different physical pairs.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: reflection moves preferred-side points farther from zero and sorting
can only increase their assigned value. Reflect other representatives first. -/
theorem radialPairGain_nonneg (f : ℝ →ᵇ ℝ) {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    0 ≤ radialPairGain f a x := by
  -- The exponential weight is decreasing in distance from zero.
  have hl (y : ℝ) (hy : y ≤ a) : 0 ≤ radialPairGain f a y := by
    rw [radialPairGain_left f a hy]
    have hd : |y| ≤ |reflect a y| := by dsimp [reflect]; grind [abs_eq_max_neg]
    exact mul_nonneg (sub_nonneg.mpr (exp_le_exp.mpr (neg_le_neg hd)))
      (sub_nonneg.mpr (le_max_left _ _))
  by_cases hx : x ≤ a
  · exact hl x hx
  · rw [← radialPairGain_reflect]
    exact hl _ (by dsimp [reflect]; linarith)

/-- The continuous pair gain is absolutely integrable.
Use: positivity at one point implies positive total gain and hence strict improvement.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: it is a sum and difference of two integrable radial integrands and their reflections. -/
theorem radialPairGain_integrable (f : ℝ →ᵇ ℝ) (a : ℝ) :
    Integrable (radialPairGain f a) :=
  ((radialIntegrand_integrable (polarizeBCF a f)).add
    ((radialIntegrand_integrable (polarizeBCF a f)).comp_sub_left (2*a))).sub
      ((radialIntegrand_integrable f).add ((radialIntegrand_integrable f).comp_sub_left (2*a)))

/-- Integrating the pair gain gives exactly twice the change of radial test integral.
Use: an actual strict pair improvement contradicts maximality on the closed orbit.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: integrate the four terms and use reflection invariance of Lebesgue measure. -/
theorem radialPairGain_integral (f : ℝ →ᵇ ℝ) (a : ℝ) :
    (∫ x, radialPairGain f a x)=2*(radialIntegral (polarizeBCF a f)-radialIntegral f) := by
  -- Reflection preserves each weighted integral when both the weight and density are reflected.
  have hp := radialIntegrand_integrable (polarizeBCF a f)
  have hf := radialIntegrand_integrable f
  unfold radialPairGain
  simp only [reflect]
  have hs := integral_sub (hp.add (hp.comp_sub_left (2*a)))
    (hf.add (hf.comp_sub_left (2*a)))
  have hpa := integral_add hp (hp.comp_sub_left (2*a))
  have hfa := integral_add hf (hf.comp_sub_left (2*a))
  simp only [Pi.add_apply,polarizeBCF_apply] at hs hpa hfa
  rw [hs,hpa,hfa]
  rw [integral_sub_left_eq_self (fun x => exp (-|x|)*polarize a f x) volume (2*a),
    integral_sub_left_eq_self (fun x => exp (-|x|)*f x) volume (2*a)]
  change radialIntegral (polarizeBCF a f)+radialIntegral (polarizeBCF a f)-
    (radialIntegral f+radialIntegral f)=_
  ring

/-- Every strict inversion across a positively centered preferred half-line strictly improves the radial integral.
Use: excludes all surviving radial value inversions in the compact orbit's maximizer.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: the pair gain is continuous, nonnegative everywhere and positive at the
inverted point; positivity of Lebesgue measure on open sets makes its integral positive. -/
theorem radialIntegral_polarize_strict (f : ℝ →ᵇ ℝ) {a x : ℝ}
    (ha : 0 < a) (hx : x < a) (hv : f x < f (reflect a x)) :
    radialIntegral f < radialIntegral (polarizeBCF a f) := by
  -- Strict preference in the exponential weight holds away from the zero-centered boundary.
  have hd : |x| < |reflect a x| := by
    have hr : 0 < reflect a x := by dsimp [reflect]; linarith
    rw [abs_of_pos hr]
    exact abs_lt.mpr ⟨by dsimp [reflect]; linarith,by dsimp [reflect]; linarith⟩
  have hg : 0 < radialPairGain f a x := by
    rw [radialPairGain_left f a hx.le,max_eq_right hv.le]
    exact mul_pos (sub_pos.mpr (exp_lt_exp.mpr (neg_lt_neg hd))) (sub_pos.mpr hv)
  have hc : Continuous (radialPairGain f a) := by
    have hp := (polarizeBCF a f).continuous
    have hr : Continuous (reflect a) := continuous_const.sub continuous_id
    exact ((continuous_exp.comp continuous_abs.neg).mul hp).add
      (((continuous_exp.comp (continuous_abs.comp hr).neg).mul (hp.comp hr))) |>.sub
        (((continuous_exp.comp continuous_abs.neg).mul f.continuous).add
          ((continuous_exp.comp (continuous_abs.comp hr).neg).mul (f.continuous.comp hr)))
  have hi := integral_pos_of_integrable_nonneg_nonzero hc (radialPairGain_integrable f a)
    (radialPairGain_nonneg f ha.le) hg.ne'
  rw [radialPairGain_integral] at hi
  linarith

/-- A density that cannot improve by centered left polarization has the corresponding point order.
Use: derives monotonicity at positive radii and half of the reflection equality for a maximizer.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: reflect x to y about their positive midpoint; a value inversion would
strictly improve the radial integral by the preceding theorem. -/
theorem radialIntegral_max_order {f : ℝ →ᵇ ℝ}
    (hf : ∀ a, 0 < a → radialIntegral (polarizeBCF a f) ≤ radialIntegral f)
    {x y : ℝ} (hxy : x < y) (hmid : 0 < x+y) : f y ≤ f x := by
  -- The positive midpoint gives exactly the preferred reflection pair required by strictness.
  by_contra h
  have hr : reflect ((x+y)/2) x=y := by dsimp [reflect]; ring
  have hi := radialIntegral_polarize_strict f (a := (x+y)/2) (x := x)
    (by linarith) (by linarith) (by rw [hr]; exact lt_of_not_ge h)
  exact (not_lt_of_ge (hf _ (by linarith))) hi

/-- The radial test integral is invariant under reflection through zero.
Use: the reflected maximizer obeys the same order condition as the original one.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: change variables x to -x and use evenness of the exponential radial weight. -/
theorem radialIntegral_mirror (f : ℝ →ᵇ ℝ) : radialIntegral (mirrorBCF f)=radialIntegral f := by
  simpa only [radialIntegral,mirrorBCF,BoundedContinuousFunction.compContinuous_apply,
    ContinuousMap.coe_mk,abs_neg] using integral_neg_eq_self (fun x : ℝ => exp (-|x|)*f x) volume

/-- Left polarization maximality forces the value at each negative point to dominate its reflection.
Use: applying the same assertion to the reflected maximizer proves evenness.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: compare -x to x+1/(n+1), then use continuity as n tends to infinity. -/
theorem radialIntegral_max_reflection {f : ℝ →ᵇ ℝ}
    (hf : ∀ a, 0 < a → radialIntegral (polarizeBCF a f) ≤ radialIntegral f)
    {x : ℝ} (hx : 0 ≤ x) : f x ≤ f (-x) := by
  -- Positive offsets keep the midpoint strictly on the preferred side while approaching the reflected point.
  have ht : Tendsto (fun n : ℕ => x+1/((n : ℝ)+1)) atTop (𝓝 x) := by
    simpa only [add_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add x
  apply le_of_tendsto (f.continuous.continuousAt.tendsto.comp ht)
  apply Eventually.of_forall
  intro n
  have hd : 0 < 1/((n : ℝ)+1) := by positivity
  exact radialIntegral_max_order hf (by linarith : -x < x+1/((n : ℝ)+1)) (by linarith)

/-- Every radial test maximizer in a regular polarization orbit is symmetric decreasing.
Use: the limiting regular rearrangement has precisely the shape needed by compactness and Transfer.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: maximality excludes strict inversions. Reflection preserves the orbit
and test integral, so the same one-sided reflection comparison applies in both directions. -/
theorem regularOrbit_maximizer_shape {f g : ℝ →ᵇ ℝ}
    (hg : g ∈ closure {q | RegularOrbit f q})
    (hmax : ∀ q ∈ closure {q | RegularOrbit f q}, radialIntegral q ≤ radialIntegral g) :
    jacobi.Variational.SymmetricDecreasing g := by
  -- Both g and its reflection maximize the same functional on the same closed orbit.
  have hp (a : ℝ) (ha : 0 < a) : radialIntegral (polarizeBCF a g) ≤ radialIntegral g :=
    hmax _ (regularOrbit_polarize hg ha.le)
  have hm (a : ℝ) (ha : 0 < a) :
      radialIntegral (polarizeBCF a (mirrorBCF g)) ≤ radialIntegral (mirrorBCF g) := by
    rw [radialIntegral_mirror]
    exact hmax _ (regularOrbit_polarize (regularOrbit_mirror hg) ha.le)
  have he (x : ℝ) (hx : 0 ≤ x) : g (-x)=g x := by
    apply le_antisymm
    · simpa only [mirrorBCF,BoundedContinuousFunction.compContinuous_apply,
        ContinuousMap.coe_mk,neg_neg] using radialIntegral_max_reflection hm hx
    · exact radialIntegral_max_reflection hp hx
  refine ⟨fun x => ?_,fun x hx y hy hxy => ?_⟩
  · rcases le_total 0 x with hx | hx
    · exact he x hx
    · simpa only [neg_neg] using (he (-x) (neg_nonneg.mpr hx)).symm
  · rcases hxy.eq_or_lt with h | h
    · exact (congrArg g h).ge
    · exact radialIntegral_max_order hp h (by linarith [show 0 < x from hx,show 0 < y from hy])

/-- An actual symmetric decreasing function belongs to the compact closure of every regular polarization orbit.
Use: supplies the radial replacement without assuming any rearrangement existence theorem.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: choose the proved radial test maximizer and apply its proved shape characterization. -/
theorem regularOrbit_radial {f : ℝ →ᵇ ℝ} {R C : ℝ} {K : ℝ≥0}
    (hR : 0 ≤ R) (hf : f ∈ regularFamily R C K) :
    ∃ g ∈ closure {q | RegularOrbit f q}, jacobi.Variational.SymmetricDecreasing g := by
  obtain ⟨g,hg,hm⟩ := regularOrbit_maximizer hR hf
  exact ⟨g,hg,regularOrbit_maximizer_shape hg hm⟩

end
end jacobi.Rearrangement
