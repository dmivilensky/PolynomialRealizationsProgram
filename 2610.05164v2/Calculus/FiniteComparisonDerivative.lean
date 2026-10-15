import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import «2610.05164v2».Calculus.ProductAtZero
import «2610.05164v2».Calculus.FiniteParameterIntegral

/-!
Article: 2610.05164v2, Proposition 13.
Differentiating an exact finite-comparison identity.
Use: `«2610.05164v2».Calculus.finite_comparison_c1` feeds
`«2610.05164v2».Primal.familyLogDeterminant_c1` (family Log Determinant c1).
Proof chain: `«2610.05164v2».Primal.familyConstraintMap_c1` — 2610.05164v2, Theorem 5.2; Contraction
implies exact feasible density, uniqueness, iteration error and energy bound.
Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral remainder
and implicit-function calculus. The needed form is proved here.
-/
namespace «2610.05164v2».Calculus
noncomputable section
open Set Metric Filter MeasureTheory Real
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/--
Defines `exponentialIncrement` of type `ℝ` by `1-exp (-L (a-b))`.

Use: `«2610.05164v2».Calculus.exponentialIncrement_derivative` uses this definition to
establish the actual Fréchet derivative: `HasFDerivAt (exponentialIncrement L b) (exp (-L
(a-b)) • L) a`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.
-/
def exponentialIncrement (L : H →L[ℝ] ℝ) (b a : H) : ℝ := 1-exp (-L (a-b))

/--
The actual Fréchet derivative: `HasFDerivAt (exponentialIncrement L b) (exp (-L (a-b)) • L) a`.

Use: `«2610.05164v2».Calculus.finite_comparison_derivative` uses this Fréchet derivative
formula to establish the actual Fréchet derivative: `HasFDerivAt F (∫ t in (0:ℝ)..1,K b b t • v
t) b`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem exponentialIncrement_derivative (L : H →L[ℝ] ℝ) (b a : H) :
    HasFDerivAt (exponentialIncrement L b) (exp (-L (a-b)) • L) a := by
  have hL := L.hasFDerivAt.comp a ((hasFDerivAt_id a).sub_const b)
  have h := ((Real.hasDerivAt_exp (-L (a-b))).comp_hasFDerivAt a hL.neg).const_sub 1
  unfold exponentialIncrement
  simpa only [id_eq,Function.comp_def,ContinuousLinearMap.comp_id,
    smul_neg,neg_neg,Pi.neg_apply] using h

variable [FiniteDimensional ℝ H]

/--
The actual Fréchet derivative: `HasFDerivAt F (∫ t in (0:ℝ)..1,K b b t • v t) b`.

Use: `«2610.05164v2».Calculus.finite_comparison_c1` uses this Fréchet derivative formula to
establish smoothness to the stated order: `ContDiff ℝ 1 F`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Prove equality of functions by evaluating both
sides at an arbitrary argument.
-/
theorem finite_comparison_derivative {F : H → ℝ} {K : H → H → ℝ → ℝ}
    {v : ℝ → H →L[ℝ] ℝ}
    (hK : Continuous (fun p : H × H × ℝ => K p.1 p.2.1 p.2.2)) (hv : Continuous v)
    (heq : ∀ a b,F a-F b=∫ t in (0:ℝ)..1,K a b t*exponentialIncrement (v t) b a)
    (b : H) : HasFDerivAt F (∫ t in (0:ℝ)..1,K b b t • v t) b := by
  -- Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
  -- at an arbitrary point in that intersection.
  let A : H → ℝ → ℝ := fun a t => K a b t*exponentialIncrement (v t) b a
  -- Establish continuity hKb before using the function at limits or in calculus arguments.
  have hKb : Continuous (fun p : H × ℝ => K p.1 b p.2) :=
    hK.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
  -- Establish continuity hE before using the function at limits or in calculus arguments.
  have hE : Continuous (fun p : H × ℝ => exponentialIncrement (v p.2) b p.1) := by
    unfold exponentialIncrement
    fun_prop
  -- Establish continuity hEd before using the function at limits or in calculus arguments.
  have hEd : Continuous (fun p : H × ℝ => exp (-(v p.2) (p.1-b)) • v p.2) := by
    fun_prop
  -- Establish continuity hA before using the function at limits or in calculus arguments.
  have hA : Continuous A.uncurry := hKb.mul hE
  obtain ⟨M,hM⟩ := (isCompact_closedBall (x:=b) (r:=1)).prod (isCompact_Icc (a:=(0:ℝ)) (b:=1)) |>.exists_bound_of_continuousOn hKb.continuousOn
  obtain ⟨B,hB⟩ := (isCompact_closedBall (x:=b) (r:=1)).prod (isCompact_Icc (a:=(0:ℝ)) (b:=1)) |>.exists_bound_of_continuousOn hEd.continuousOn
  have hM0 : 0≤M := (norm_nonneg _).trans (hM (b,0) ⟨mem_closedBall_self (by norm_num),by norm_num⟩)
  have hEb (t : ℝ) : exponentialIncrement (v t) b b=0 := by simp [exponentialIncrement]
  have hEbound (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (a : H) (ha : a∈ball b 1) :
      ‖exponentialIncrement (v t) b a‖≤B*‖a-b‖ := by
    have h := (convex_ball b 1).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun a _ => (exponentialIncrement_derivative (v t) b a).hasFDerivWithinAt)
      (fun a ha => hB (a,t) ⟨ball_subset_closedBall ha,ht⟩)
      (mem_ball_self (by norm_num)) ha
    simpa only [hEb,sub_zero] using h
  have hdom (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (a : H) (ha : a∈ball b 1) :
      ‖A a t-A b t‖≤(M*B)*‖a-b‖ := by
    simp only [A,hEb,mul_zero,sub_zero,norm_mul]
    calc
      ‖K a b t‖*‖exponentialIncrement (v t) b a‖≤M*(B*‖a-b‖) :=
        mul_le_mul (hM (a,t) ⟨ball_subset_closedBall ha,ht⟩) (hEbound t ht a ha)
          (norm_nonneg _) hM0
      _=(M*B)*‖a-b‖ := by ring
  have hD (t : ℝ) : HasFDerivAt (fun a => A a t) (K b b t • v t) b := by
    -- Establish continuity hKt before using the function at limits or in calculus arguments.
    have hKt : Continuous (fun a : H => K a b t) :=
      hKb.comp (continuous_id.prodMk continuous_const)
    have h := product_hasFDerivAt_at_zero (exponentialIncrement_derivative (v t) b b)
      (hEb t) hKt.continuousAt
    simpa only [A,sub_self,map_zero,neg_zero,exp_zero,one_smul] using h
  -- Establish continuity hG before using the function at limits or in calculus arguments.
  have hG : Continuous (fun t => K b b t • v t) :=
    (hK.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))).smul hv
  -- Establish hInt as the integrability justification for the later integral estimates or
  -- changes of order.
  have hInt : Integrable (A b) (volume.restrict (Ioc (0:ℝ) 1)) := by
    have hzero : A b=fun _ => (0:ℝ) := by funext t;simp [A,hEb]
    rw [hzero]
    exact integrable_zero _ _ _
  have h := (hasFDerivAt_integral_of_dominated_loc_of_lip'
    (F:=A) (μ:=volume.restrict (Ioc (0:ℝ) 1)) (s:=ball b 1) (bound:=fun _ => M*B)
    (ball_mem_nhds b (by norm_num))
    (fun a _ => (show Continuous (A a) from hA.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    hInt hG.aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact fun a ha => hdom t ⟨ht.1.le,ht.2⟩ a ha)
    (integrableOn_const (by simp)) (Eventually.of_forall hD)).2
  have h' : HasFDerivAt (fun a => ∫ t in (0:ℝ)..1,A a t)
      (∫ t in (0:ℝ)..1,K b b t • v t) b := by
    simpa only [intervalIntegral.integral_of_le zero_le_one] using h
  have hfull : F=fun a => (∫ t in (0:ℝ)..1,A a t)+F b := by
    funext a
    have hh := heq a b
    dsimp [A]
    linarith
  rw [hfull]
  exact h'.add_const (F b)

/--
Smoothness to the stated order: `ContDiff ℝ 1 F`.

Use: `«2610.05164v2».Primal.familyLogDeterminant_c1` uses this assertion to establish
smoothness to the stated order: `ContDiff ℝ 1 (familyLogDeterminant hψ hθ hκ s)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Source: mathlib, Mathlib.Analysis.Calculus — parameter differentiation, Taylor integral
remainder and implicit-function calculus.

Proof: Use the identities/estimates `«2610.05164v2».Calculus.finite_comparison_derivative` with
the arguments shown in the proof.
-/
theorem finite_comparison_c1 {F : H → ℝ} {K : H → H → ℝ → ℝ}
    {v : ℝ → H →L[ℝ] ℝ}
    (hK : Continuous (fun p : H × H × ℝ => K p.1 p.2.1 p.2.2)) (hv : Continuous v)
    (heq : ∀ a b,F a-F b=∫ t in (0:ℝ)..1,K a b t*exponentialIncrement (v t) b a) :
    ContDiff ℝ 1 F := by
  -- Use the identities/estimates `«2610.05164v2».Calculus.finite_comparison_derivative` with
  -- the arguments shown in the proof.
  refine contDiff_one_iff_hasFDerivAt.mpr ⟨fun b => ∫ t in (0:ℝ)..1,K b b t • v t,?_,
    finite_comparison_derivative hK hv heq⟩
  -- Establish continuity hG before using the function at limits or in calculus arguments.
  have hG : Continuous (fun p : H × ℝ => K p.1 p.1 p.2 • v p.2) :=
    (hK.comp (continuous_fst.prodMk (continuous_fst.prodMk continuous_snd))).smul
      (hv.comp continuous_snd)
  simpa only [Function.comp_def,id_eq] using
    (intervalIntegral.continuous_parametric_primitive_of_continuous (a₀:=(0:ℝ)) hG).comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : H => (1:ℝ))))

end
end «2610.05164v2».Calculus
