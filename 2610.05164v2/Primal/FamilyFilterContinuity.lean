import «2610.05164v2».Primal.FamilyEnergyBound
import «2610.05164v2».Primal.RightFilterParameterStability
import «2610.05164v2».Primal.LinearParameterStability
import «2610.05164v2».Calculus.UniformParameterContinuity

/-!
Article: 2610.05164v2, Proposition 13.
Joint continuity of the actual primal filters in all parameters and the regular coordinate.
Use: `«2610.05164v2».Primal.familyLinearFilter_joint_continuous` feeds
`«2610.05164v2».Primal.familyTraceComparison_continuous` (family Trace Comparison continuous).
Proof chain: `«2610.05164v2».Primal.familyConstraintMap_c1` — 2610.05164v2, Theorem 5.2; Contraction
implies exact feasible density, uniqueness, iteration error and energy bound.
-/
namespace «2610.05164v2».Primal
noncomputable section
open Set Real
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

/--
The stated quantitative bound `|y-z|≤(K-1)*(1+B)`.

Use: `«2610.05164v2».Primal.familyNonlinearFilter_parameter_bound` uses this bound to establish
the stated quantitative bound `|familyNonlinearFilter hψ hθ κ s reflected a
t-familyNonlinearFilter hψ hθ κ s reflected b t|≤ (exp (‖a-b‖*∑ i,‖unitDirection (hθ
i)‖)-1)*(1+2*s/κ)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Expand/rewrite the named definitions and identities appearing in the tactic block; the
remaining goal is a direct simplification or algebraic consequence.
-/
theorem shifted_pair_difference_bound {y z K B : ℝ} (hK : 1≤K)
    (hy : y≤B) (hz : z≤B) (hyz : 1+y≤K*(1+z)) (hzy : 1+z≤K*(1+y)) :
    |y-z|≤(K-1)*(1+B) := by
  have h1 := mul_le_mul_of_nonneg_left hy (sub_nonneg.mpr hK)
  have h2 := mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr hK)
  rw [abs_le]
  constructor <;> nlinarith

/--
Defines `familyNonlinearFilter` of type `ℝ` by `if reflected then reflectedNonlinearFilter
(affineProfile_continuous hψ hθ a) κ s (unitClamp t) else nonlinearFilter
(affineProfile_continuous hψ hθ a) κ s (unitClamp t)`.

Use: `«2610.05164v2».Primal.familyNonlinearFilter_parameter_bound` uses this definition to
establish the stated quantitative bound `|familyNonlinearFilter hψ hθ κ s reflected a
t-familyNonlinearFilter hψ hθ κ s reflected b t|≤ (exp (‖a-b‖*∑ i,‖unitDirection (hθ
i)‖)-1)*(1+2*s/κ)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.
-/
def familyNonlinearFilter {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) (κ s : ℝ) (reflected : Bool)
    (a : ι → ℝ) (t : ℝ) : ℝ :=
  if reflected then reflectedNonlinearFilter (affineProfile_continuous hψ hθ a) κ s (unitClamp t)
  else nonlinearFilter (affineProfile_continuous hψ hθ a) κ s (unitClamp t)

/--
The stated quantitative bound `|familyNonlinearFilter hψ hθ κ s reflected a
t-familyNonlinearFilter hψ hθ κ s reflected b t|≤ (exp (‖a-b‖*∑ i,‖unitDirection (hθ
i)‖)-1)*(1+2*s/κ)`.

Use: `«2610.05164v2».Primal.familyNonlinearFilter_joint_continuous` uses this bound to
establish continuity of the displayed function: `Continuous (familyNonlinearFilter hψ hθ κ s
reflected).uncurry`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».Primal.affine_profile_difference_bound`,
`«2610.05164v2».Primal.unitClamp_mem`, `«2610.05164v2».Primal.affineProfile_continuous` with
the arguments shown in the proof.
-/
theorem familyNonlinearFilter_parameter_bound {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ s : ℝ} (hκ : 0<κ) (hs : 0≤s)
    (reflected : Bool) (a b : ι → ℝ) (t : ℝ) :
    |familyNonlinearFilter hψ hθ κ s reflected a t-familyNonlinearFilter hψ hθ κ s reflected b t|≤
      (exp (‖a-b‖*∑ i,‖unitDirection (hθ i)‖)-1)*(1+2*s/κ) := by
  -- Use the identities/estimates `«2610.05164v2».Primal.affine_profile_difference_bound`,
  -- `«2610.05164v2».Primal.unitClamp_mem`, `«2610.05164v2».Primal.affineProfile_continuous`
  -- with the arguments shown in the proof.
  let d : ℝ := ‖a-b‖*∑ i,‖unitDirection (hθ i)‖
  have hd : 0≤d := mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hp : ∀ u∈Icc (0:ℝ) 1,|affineProfile ψ θ a u-affineProfile ψ θ b u|≤d :=
    fun u hu => affine_profile_difference_bound ψ hθ a b hu
  have hp' : ∀ u∈Icc (0:ℝ) 1,|affineProfile ψ θ b u-affineProfile ψ θ a u|≤d := by
    intro u hu
    rw [abs_sub_comm]
    exact hp u hu
  have hu := unitClamp_mem t
  have hsk : 0≤s/κ := div_nonneg hs hκ.le
  have hB (c : ι → ℝ) : familyNonlinearFilter hψ hθ κ s reflected c t≤2*s/κ := by
    cases reflected with
    | false =>
      have hb := nonlinearFilter_bound (affineProfile_continuous hψ hθ c) hκ hs hu
      have hh := mul_le_mul_of_nonneg_left
        ((show (unitClamp t)^3≤1 from pow_le_one₀ hu.1 hu.2).trans (by norm_num : (1:ℝ)≤2)) hsk
      exact hb.trans (by convert hh using 1;ring)
    | true =>
      have hb := reflectedNonlinearFilter_bound (affineProfile_continuous hψ hθ c) hκ hs hu
      have hh := mul_le_mul_of_nonneg_left (show 2-(unitClamp t)^3≤2 by linarith [pow_nonneg hu.1 3]) hsk
      exact hb.trans (by convert hh using 1;ring)
  have hpair :
      1+familyNonlinearFilter hψ hθ κ s reflected a t≤exp d*(1+familyNonlinearFilter hψ hθ κ s reflected b t) ∧
      1+familyNonlinearFilter hψ hθ κ s reflected b t≤exp d*(1+familyNonlinearFilter hψ hθ κ s reflected a t) := by
    cases reflected with
    | false => exact ⟨(nonlinearFilter_parameter_enclosed (affineProfile_continuous hψ hθ a)
        (affineProfile_continuous hψ hθ b) hκ hs hd hp hu).2,
        (nonlinearFilter_parameter_enclosed (affineProfile_continuous hψ hθ b)
        (affineProfile_continuous hψ hθ a) hκ hs hd hp' hu).2⟩
    | true => exact ⟨(reflectedNonlinearFilter_parameter_enclosed (affineProfile_continuous hψ hθ a)
        (affineProfile_continuous hψ hθ b) hκ hs hd hp hu).2,
        (reflectedNonlinearFilter_parameter_enclosed (affineProfile_continuous hψ hθ b)
        (affineProfile_continuous hψ hθ a) hκ hs hd hp' hu).2⟩
  exact shifted_pair_difference_bound (one_le_exp_iff.mpr hd) (hB a) (hB b) hpair.1 hpair.2

/--
Continuity of the displayed function: `Continuous (familyNonlinearFilter hψ hθ κ s
reflected).uncurry`.

Use: `«2610.05164v2».Primal.familyDeterminantComparison_continuous` uses this continuity result
to establish continuity of the displayed function: `Continuous (fun p : (ι → ℝ) × (ι → ℝ) × ℝ
=> familyDeterminantComparison hψ hθ κ s p.1 p.2.1 p.2.2)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates
`«2610.05164v2».Calculus.continuous_of_uniform_parameter_modulus`,
`«2610.05164v2».Primal.affineProfile_continuous`,
`«2610.05164v2».Primal.nonlinearFilter_continuous` with the arguments shown in the proof.
-/
theorem familyNonlinearFilter_joint_continuous {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ s : ℝ} (hκ : 0<κ) (hs : 0≤s)
    (reflected : Bool) : Continuous (familyNonlinearFilter hψ hθ κ s reflected).uncurry := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calculus.continuous_of_uniform_parameter_modulus`,
  -- `«2610.05164v2».Primal.affineProfile_continuous`,
  -- `«2610.05164v2».Primal.nonlinearFilter_continuous` with the arguments shown in the proof.
  apply «2610.05164v2».Calculus.continuous_of_uniform_parameter_modulus
  · intro a
    cases reflected with
    | false => exact (nonlinearFilter_continuous (affineProfile_continuous hψ hθ a) hκ hs).comp unitClamp_continuous
    | true => exact (reflectedNonlinearFilter_continuous (affineProfile_continuous hψ hθ a) hκ hs).comp unitClamp_continuous
  · intro b
    refine ⟨fun a => (exp (‖a-b‖*∑ i,‖unitDirection (hθ i)‖)-1)*(1+2*s/κ),?_,?_,?_⟩
    · fun_prop
    · simp
    · exact fun a t => familyNonlinearFilter_parameter_bound hψ hθ hκ hs reflected a b t

/--
Defines `familyLinearFilter` of type `ℝ` by `if reflected then reflectedLinearFilter
(affineProfile_continuous hψ hθ a) κ (unitClamp t) else linearFilter (affineProfile_continuous
hψ hθ a) κ (unitClamp t)`.

Use: `«2610.05164v2».Primal.familyLinearFilter_parameter_bound` uses this definition to
establish the stated quantitative bound `|familyLinearFilter hψ hθ κ reflected a
t-familyLinearFilter hψ hθ κ reflected b t|≤ 2*(exp (‖a-b‖*∑ i,‖unitDirection (hθ i)‖)-1)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.
-/
def familyLinearFilter {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) (κ : ℝ) (reflected : Bool)
    (a : ι → ℝ) (t : ℝ) : ℝ :=
  if reflected then reflectedLinearFilter (affineProfile_continuous hψ hθ a) κ (unitClamp t)
  else linearFilter (affineProfile_continuous hψ hθ a) κ (unitClamp t)

/--
The stated quantitative bound `|familyLinearFilter hψ hθ κ reflected a t-familyLinearFilter hψ
hθ κ reflected b t|≤ 2*(exp (‖a-b‖*∑ i,‖unitDirection (hθ i)‖)-1)`.

Use: `«2610.05164v2».Primal.familyLinearFilter_joint_continuous` uses this bound to establish
continuity of the displayed function: `Continuous (familyLinearFilter hψ hθ κ
reflected).uncurry`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».Primal.affine_profile_difference_bound`,
`«2610.05164v2».Primal.unitClamp_mem`, `«2610.05164v2».Primal.affineProfile_continuous` with
the arguments shown in the proof.
-/
theorem familyLinearFilter_parameter_bound {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ : ℝ} (hκ : 0<κ)
    (reflected : Bool) (a b : ι → ℝ) (t : ℝ) :
    |familyLinearFilter hψ hθ κ reflected a t-familyLinearFilter hψ hθ κ reflected b t|≤
      2*(exp (‖a-b‖*∑ i,‖unitDirection (hθ i)‖)-1) := by
  -- Use the identities/estimates `«2610.05164v2».Primal.affine_profile_difference_bound`,
  -- `«2610.05164v2».Primal.unitClamp_mem`, `«2610.05164v2».Primal.affineProfile_continuous`
  -- with the arguments shown in the proof.
  let d : ℝ := ‖a-b‖*∑ i,‖unitDirection (hθ i)‖
  have hd : 0≤d := mul_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hp : ∀ u∈Icc (0:ℝ) 1,|affineProfile ψ θ a u-affineProfile ψ θ b u|≤d :=
    fun u hu => affine_profile_difference_bound ψ hθ a b hu
  have hu := unitClamp_mem t
  have hK : 0≤exp d-1 := sub_nonneg.mpr (one_le_exp_iff.mpr hd)
  change |familyLinearFilter hψ hθ κ reflected a t-familyLinearFilter hψ hθ κ reflected b t|≤2*(exp d-1)
  cases reflected with
  | false =>
    have he := linearFilter_parameter_bound (affineProfile_continuous hψ hθ a)
      (affineProfile_continuous hψ hθ b) hκ hd hp hu
    unfold linearDefect at he
    have hb : (unitClamp t)^3-linearFilter (affineProfile_continuous hψ hθ b) κ (unitClamp t)≤2 := by
      linarith [show (unitClamp t)^3≤1 from pow_le_one₀ hu.1 hu.2,
        linearFilter_nonneg (affineProfile_continuous hψ hθ b) hκ (unitClamp t)]
    exact he.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb hK)
  | true =>
    have he := reflectedLinearFilter_parameter_bound (affineProfile_continuous hψ hθ a)
      (affineProfile_continuous hψ hθ b) hκ hd hp hu
    have hb : 2-(unitClamp t)^3-reflectedLinearFilter (affineProfile_continuous hψ hθ b) κ (unitClamp t)≤2 := by
      linarith [pow_nonneg hu.1 3,reflectedLinearFilter_nonneg (affineProfile_continuous hψ hθ b) hκ (unitClamp t)]
    exact he.trans (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb hK)

/--
Continuity of the displayed function: `Continuous (familyLinearFilter hψ hθ κ
reflected).uncurry`.

Use: `«2610.05164v2».Primal.familyTraceComparison_continuous` uses this continuity result to
establish continuity of the displayed function: `Continuous (fun p : (ι → ℝ) × (ι → ℝ) × ℝ =>
familyTraceComparison hψ hθ κ p.1 p.2.1 p.2.2)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates
`«2610.05164v2».Calculus.continuous_of_uniform_parameter_modulus`,
`«2610.05164v2».Primal.affineProfile_continuous`,
`«2610.05164v2».Primal.linearFilter_continuous` with the arguments shown in the proof.
-/
theorem familyLinearFilter_joint_continuous {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ : ℝ} (hκ : 0<κ)
    (reflected : Bool) : Continuous (familyLinearFilter hψ hθ κ reflected).uncurry := by
  -- Use the identities/estimates
  -- `«2610.05164v2».Calculus.continuous_of_uniform_parameter_modulus`,
  -- `«2610.05164v2».Primal.affineProfile_continuous`,
  -- `«2610.05164v2».Primal.linearFilter_continuous` with the arguments shown in the proof.
  apply «2610.05164v2».Calculus.continuous_of_uniform_parameter_modulus
  · intro a
    cases reflected with
    | false => exact (linearFilter_continuous (affineProfile_continuous hψ hθ a) hκ).comp unitClamp_continuous
    | true => exact (reflectedLinearFilter_continuous (affineProfile_continuous hψ hθ a) hκ).comp unitClamp_continuous
  · intro b
    refine ⟨fun a => 2*(exp (‖a-b‖*∑ i,‖unitDirection (hθ i)‖)-1),?_,?_,?_⟩
    · fun_prop
    · simp
    · exact fun a t => familyLinearFilter_parameter_bound hψ hθ hκ reflected a b t

end
end «2610.05164v2».Primal
