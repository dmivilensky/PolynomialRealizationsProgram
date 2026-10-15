import «2610.05164v2».LocalObstruction.TailGradient

/-!
Article: 2610.05164v2, Theorem 6.1.
Theorem 6.1's finite-dimensional chain rule and neighborhood conclusion.
Use: `«2610.05164v2».LocalObstruction.finite_observation_no_local_bound_with_property` feeds
`«2610.05164v2».LocalObstruction.finite_observation_no_local_bound` (finite observation no local
bound).
Proof chain: `«2610.05164v2».LocalObstruction.theorem_6_1` — 2610.05164v2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace «2610.05164v2».LocalObstruction
noncomputable section
open Set MeasureTheory Real Filter «2610.05164v2».SineContinuum
open scoped Topology ContDiff
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 /--
Constructs witnesses with the exact properties `∃ f : ℝ → ℝ, ContDiff ℝ ∞ (fun x => f x-m x) ∧
HasCompactSupport (fun x => f x-m x) ∧ (∀ x,0≤f x) ∧ (∫ x,f x)=1 ∧ (∫ x,sqrt (f x))=1 ∧ (∀ x,|f
x-m x|<ε) ∧ ((fun i => O i f)∈U ∧ Q f) ∧ densityEnergy f<Φ (fun i => O i f)`.

Use: `«2610.05164v2».LocalObstruction.finite_observation_no_local_bound` uses this identity to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 6.1 via `«2610.05164v2».LocalObstruction.theorem_6_1`.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral. Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem finite_observation_no_local_bound_with_property {ι : Type*} [Fintype ι]
    (O : ι → (ℝ → ℝ) → ℝ) (W : ∀ i,ObservationWitness (O i))
    {U : Set (ι → ℝ)} (hU : U∈𝓝 (fun i => O i m)) (Φ : (ι → ℝ) → ℝ)
    (hΦ : ContDiffAt ℝ 1 Φ (fun i => O i m))
    (heq : Φ (fun i => O i m)=densityEnergy m)
    (Q : (ℝ → ℝ) → Prop)
    (hQ : ∀ v w : SmoothTest, 0<(∫ x,n x*w x) →
      ∀ᶠ t in 𝓝 (0:ℝ),Q (curveDensity (amplitudeDirection v) w t))
    {ε : ℝ} (hε : 0<ε) :
    ∃ f : ℝ → ℝ,
      ContDiff ℝ ∞ (fun x => f x-m x) ∧ HasCompactSupport (fun x => f x-m x) ∧
      (∀ x,0≤f x) ∧ (∫ x,f x)=1 ∧ (∫ x,sqrt (f x))=1 ∧
      (∀ x,|f x-m x|<ε) ∧ ((fun i => O i f)∈U ∧ Q f) ∧ densityEnergy f<Φ (fun i => O i f) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  classical
  let L := fderiv ℝ Φ (fun i => O i m)
  let c := fun i => L (Pi.single i 1)
  let g := TailGradient.sum (fun i => (W i).gradient) c
  have hL (a : ι → ℝ) : L a=∑ i,c i*a i := by
    have ha : a=∑ i,a i • Pi.single i (1:ℝ) := by
      ext j
      simp [Finset.sum_apply,Pi.single_apply]
    conv_lhs => rw [ha,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul,smul_eq_mul]
    change a i*c i=c i*a i
    ring
  have hgrad (v : SmoothTest) : L (fun i => ∫ x,v x*(W i).gradient.value x)=∫ x,v x*g.value x := by
    rw [hL]
    have hf : (fun x => v x*g.value x)=fun x => ∑ i,c i*(v x*(W i).gradient.value x) := by
      funext x
      change v x*(∑ i,c i*(W i).gradient.value x)=_
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hf,integral_finsetSum _ (fun i _ => (test_integrable v (W i).gradient.continuous).const_mul (c i))]
    simp only [integral_const_mul]
  have hcurve (v w : SmoothTest) (hw : 0<∫ x,n x*w x) :
      HasDerivAt (fun t => (fun i => O i (curveDensity (amplitudeDirection v) w t)))
        (fun i => ∫ x,v x*(W i).gradient.value x) 0 :=
    hasDerivAt_pi.mpr (fun i => (W i).curve_derivative v w hw)
  apply no_local_lower_bound_of_gradient_with_property g.continuous g.tail heq
    (P := fun f => (fun i => O i f)∈U ∧ Q f) (hε := hε)
  · intro v w hw
    have h := hΦ.differentiableAt (by norm_num : (1:ℕ∞ω)≠0) |>.hasFDerivAt
    have ht := h.comp_hasDerivAt_of_eq (0:ℝ) (hcurve v w hw) (by simp only [curveDensity_zero])
    rw [hgrad] at ht
    exact ht
  · intro v w hw
    -- Record the convergence ht with its source filter and target limit before taking limits
    -- in the subsequent identities/bounds.
    have ht : Tendsto (fun t => (fun i => O i (curveDensity (amplitudeDirection v) w t)))
        (𝓝 0) (𝓝 (fun i => O i m)) := by
      convert! (hcurve v w hw).continuousAt.tendsto using 1
      simp only [curveDensity_zero]
    exact (ht.eventually hU).and (hQ v w hw)

 /--
Constructs witnesses with the exact properties `∃ f : ℝ → ℝ, ContDiff ℝ ∞ (fun x => f x-m x) ∧
HasCompactSupport (fun x => f x-m x) ∧ (∀ x,0≤f x) ∧ (∫ x,f x)=1 ∧ (∫ x,sqrt (f x))=1 ∧ (∀ x,|f
x-m x|<ε) ∧ (fun i => O i f)∈U ∧ densityEnergy f<Φ (fun i => O i f)`.

Use: a standalone supporting identity for the article chain below; no retained declaration
currently has an explicit proof dependency on it.

Article: 2610.05164v2, Theorem 6.1.

Proof: Use the identities/estimates
`«2610.05164v2».LocalObstruction.finite_observation_no_local_bound_with_property` with the
arguments shown in the proof.
-/
theorem finite_observation_no_local_bound {ι : Type*} [Fintype ι]
    (O : ι → (ℝ → ℝ) → ℝ) (W : ∀ i,ObservationWitness (O i))
    {U : Set (ι → ℝ)} (hU : U∈𝓝 (fun i => O i m)) (Φ : (ι → ℝ) → ℝ)
    (hΦ : ContDiffAt ℝ 1 Φ (fun i => O i m))
    (heq : Φ (fun i => O i m)=densityEnergy m) {ε : ℝ} (hε : 0<ε) :
    ∃ f : ℝ → ℝ,
      ContDiff ℝ ∞ (fun x => f x-m x) ∧ HasCompactSupport (fun x => f x-m x) ∧
      (∀ x,0≤f x) ∧ (∫ x,f x)=1 ∧ (∫ x,sqrt (f x))=1 ∧
      (∀ x,|f x-m x|<ε) ∧ (fun i => O i f)∈U ∧ densityEnergy f<Φ (fun i => O i f) := by
  -- Use the identities/estimates
  -- `«2610.05164v2».LocalObstruction.finite_observation_no_local_bound_with_property` with the
  -- arguments shown in the proof.
  obtain ⟨f,hc,hs,hn,hm,hr,hsmall,⟨ho,_⟩,hless⟩ :=
    finite_observation_no_local_bound_with_property O W hU Φ hΦ heq (fun _ => True)
      (fun _ _ _ => Filter.Eventually.of_forall (fun _ => trivial)) hε
  exact ⟨f,hc,hs,hn,hm,hr,hsmall,ho,hless⟩

end
end «2610.05164v2».LocalObstruction
