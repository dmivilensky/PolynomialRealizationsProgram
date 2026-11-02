import krylov.XR.ConditionalPhysical

/-!
Article: main_krylov, prop:cond, original physical attaining fibres.
Use: the exact conditional maxima are achieved by actual own-time
observed operator sequences on fixed identity steps, preserving all
original budgets and the original revealed or unrevealed base convention.
Source: the proved physical observation, budget and model-error identities.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Secant
open scoped Matrix.Norms.L2Operator

/-- The original old physical increment is the genuine congruence of
its printed compressed completion matrix. Article: prop:cond. -/
theorem conditionalPhysical_old_increment (r y δ k : ℝ) (E : Matrix (Fin 2) (Fin 2) ℝ) :
    conditionalPhysicalSequence r y δ k E 1-conditionalPhysicalSequence r y δ k E 0=
      conditionalPhysicalRoot r*conditionalMatrix y δ k*conditionalPhysicalRoot r := by
  simp only [conditionalPhysicalSequence,one_ne_zero,ite_false,ite_true,zero_ne_one,
    Matrix.mul_add,Matrix.add_mul,Matrix.mul_one]
  abel

/-- The original fresh physical increment is independently the true
congruence of its admitted fresh matrix. Article: main_krylov, prop:cond. -/
theorem conditionalPhysical_fresh_increment (r y δ k : ℝ) (E : Matrix (Fin 2) (Fin 2) ℝ) :
    conditionalPhysicalSequence r y δ k E 2-conditionalPhysicalSequence r y δ k E 1=
      conditionalPhysicalRoot r*E*conditionalPhysicalRoot r := by
  simp only [conditionalPhysicalSequence,OfNat.ofNat_ne_zero,ite_false,one_ne_zero,
    ite_true,show (2 : ℕ)≠1 by omega]
  abel

/-- The normalized construction uses the genuine positive root of its
physical base, not just a norm-equivalent arbitrary whitening.
Article: main_krylov, prop:cond. -/
theorem conditionalPhysical_canonical_increment (r : ℝ) (hr : 0<r)
    (X : Matrix (Fin 2) (Fin 2) ℝ) :
    relativeOperator (conditionalPhysicalRoot r*conditionalPhysicalRoot r)
      (conditionalPhysicalRoot r*X*conditionalPhysicalRoot r)=X := by
  have hu := conditionalPhysicalRoot_det_unit r hr.ne'
  unfold relativeOperator
  rw [conditionalPhysicalRoot_canonical r hr.le]
  rw [←Matrix.mul_assoc,←Matrix.mul_assoc,nonsing_inv_mul _ hu,one_mul,
    Matrix.mul_assoc,mul_nonsing_inv _ hu,Matrix.mul_one]

/-- The exact known-base conditional maximum is attained by genuine
physical operator sequences with one fixed revealed positive base.
Article: main_krylov, prop:cond(a), sharpness in n=2. -/
theorem physical_known_conditional_radius {ω δ k fresh : ℝ} (hω : 0<ω)
    (hfeasible : δ^2+k^2≤ω^2) (hfresh : 0≤fresh) :
    IsGreatest {v : ℝ | ∃ y : ℝ,∃ E : Matrix (Fin 2) (Fin 2) ℝ,
      ‖conditionalMatrix y δ k‖≤ω ∧ E.IsSymm ∧ ‖E‖≤fresh ∧
      v=relativeBudget (conditionalPhysicalRoot 1*conditionalPhysicalRoot 1)
        (conditionalPhysicalSequence 1 y δ k E 2-latest (conditionalPhysicalObservation 1 y δ k E))}
      (knownConditionalRadius ω δ k fresh) := by
  have hh := knownConditionalRadius_isGreatest hω hfeasible hfresh
  constructor
  · obtain ⟨y,E,hy,hs,hE,hv⟩ := hh.1
    refine ⟨y,E,hy,hs,hE,?_⟩
    rw [conditionalPhysical_model_radius 1 y δ k one_ne_zero E hs]
    exact hv
  · rintro v ⟨y,E,hy,hs,hE,rfl⟩
    rw [conditionalPhysical_model_radius 1 y δ k one_ne_zero E hs]
    exact hh.2 ⟨y,E,hy,hs,hE,rfl⟩

/-- The exact data-only conditional maximum is attained by actual
physical operator explanations with the same original signed observed
matrix and the same fixed physical identity steps.
Article: main_krylov, prop:cond(b), sharpness in n=2. -/
theorem physical_unknown_conditional_radius {ω δobs fresh : ℝ} (hω : 0<ω) (hω₁ : ω<1)
    (hfeasible : δobs^2≤2-2*Real.sqrt (1-ω^2)) (hfresh : 0≤fresh) :
    IsGreatest {v : ℝ | ∃ k y : ℝ,∃ E : Matrix (Fin 2) (Fin 2) ℝ,
      0<1+k ∧ ‖conditionalMatrix y (observedConditionalCross δobs k) k‖≤ω ∧
      E.IsSymm ∧ ‖E‖≤fresh ∧
      let r := (Real.sqrt (1+k))⁻¹
      v=relativeBudget (conditionalPhysicalRoot r*conditionalPhysicalRoot r)
        (conditionalPhysicalSequence r y (observedConditionalCross δobs k) k E 2-
          latest (conditionalPhysicalObservation r y (observedConditionalCross δobs k) k E))}
      (unknownConditionalRadius ω δobs fresh) := by
  have hh := signed_conditional_full_radius hω hω₁ hfeasible hfresh
  constructor
  · obtain ⟨y,E,⟨k,hk,hb⟩,hs,hE,hv⟩ := hh.1
    refine ⟨k,y,E,hk,hb,hs,hE,?_⟩
    dsimp only
    rw [conditionalPhysical_model_radius _ y _ k
      (inv_ne_zero (Real.sqrt_pos.mpr hk).ne') E hs]
    exact hv
  · rintro v ⟨k,y,E,hk,hb,hs,hE,hv⟩
    dsimp only at hv
    rw [conditionalPhysical_model_radius _ y _ k
      (inv_ne_zero (Real.sqrt_pos.mpr hk).ne') E hs] at hv
    exact hh.2 ⟨y,E,⟨k,hk,hb⟩,hs,hE,hv⟩

/-- At zero old variation the full physical conditional radius is just
the true fresh allowance, with no artificial strict-pivot assumption.
Article: main_krylov, prop:cond, omega_0=0. -/
theorem conditional_zero_full_radius {fresh : ℝ} (hfresh : 0≤fresh) :
    IsGreatest {v : ℝ | ∃ y : ℝ,∃ E : Matrix (Fin 2) (Fin 2) ℝ,
      ‖conditionalMatrix y 0 0‖≤0 ∧ E.IsSymm ∧ ‖E‖≤fresh ∧
      v=‖conditionalHiddenError y+E‖} fresh := by
  have hp : IsGreatest {v : ℝ | ∃ y : ℝ,‖conditionalMatrix y 0 0‖≤0 ∧ v=|y|} 0 := by
    constructor
    · refine ⟨0,?_,by simp⟩
      have hz : conditionalMatrix 0 0 0=0 := by ext i j; fin_cases i <;> fin_cases j <;> simp [conditionalMatrix]
      simp only [hz,norm_zero,le_refl]
    · rintro v ⟨y,hy,rfl⟩
      exact ((conditionalMatrix_zero_cross_iff y 0 0 le_rfl).mp hy).1
  simpa only [zero_add] using conditional_fresh_radius _ 0 fresh hfresh hp

end
end krylov.XR
