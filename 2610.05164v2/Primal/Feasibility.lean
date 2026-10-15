import «2610.05164v2».Primal.ArticleFamily

/-!
Article: 2610.05164v2, Theorem 5.2.
The analytic part of Theorem 5.2.
Result: `«2610.05164v2».Primal.exact_primal_family_of_contraction` supplies the stated article
conclusion.
-/
namespace «2610.05164v2».Primal
noncomputable section
open Set Metric Filter Real MeasureTheory
open scoped Topology NNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

/--
Defines the alternatives used to distinguish the cases in the subsequent construction.

Use: `«2610.05164v2».Primal.exact_primal_family_of_contraction` uses this definition to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.
-/
inductive FamilyObservation where
  /-- The integral of density^(j/2), with j>0 so the family moment-regularity theorem applies. -/
  | moment (j : ℕ) (positive : 0<j)
  /-- The family spectral log determinant at the specified nonnegative observation scale. -/
  | determinant (s : ℝ) (nonnegative : 0≤s)
  /-- The actual spectral square-trace observation of the family density. -/
  | squareTrace

/--
Defines `familyObservation` of type `ℝ` by `match observation with | .moment j _ => ∫
x,(speedData (affineProfile ψ θ a) (affineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2) |
.determinant s _ => familyLogDeterminant hψ hθ hκ s a | .squareTrace => familySquareTrace hψ hθ
hκ a`.

Use: `«2610.05164v2».Primal.exact_primal_family_of_contraction` uses this definition to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.
-/
def familyObservation {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ : ℝ} (hκ : 0<κ)
    (observation : FamilyObservation) (a : ι → ℝ) : ℝ :=
  match observation with
  | .moment j _ => ∫ x,(speedData (affineProfile ψ θ a)
      (affineProfile_continuous hψ hθ a)).density κ x^((j:ℝ)/2)
  | .determinant s _ => familyLogDeterminant hψ hθ hκ s a
  | .squareTrace => familySquareTrace hψ hθ hκ a

/--
Smoothness to the stated order: `ContDiff ℝ 1 (familyObservation hψ hθ hκ observation)`.

Use: `«2610.05164v2».Primal.familyConstraintMap_c1` uses this assertion to establish smoothness
to the stated order: `ContDiff ℝ 1 (familyConstraintMap hψ hθ hκ observations targets)`.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.

Proof: Use the identities/estimates `«2610.05164v2».Primal.density_family_moment_c1`,
`«2610.05164v2».Primal.familyLogDeterminant_c1`, `«2610.05164v2».Primal.familySquareTrace_c1`
with the arguments shown in the proof.
-/
theorem familyObservation_c1 {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ : ℝ} (hκ : 0<κ)
    (observation : FamilyObservation) : ContDiff ℝ 1 (familyObservation hψ hθ hκ observation) := by
  cases observation with
  | moment j hj => exact density_family_moment_c1 hψ hθ hκ hj
  | determinant s hs => exact familyLogDeterminant_c1 hψ hθ hκ hs
  | squareTrace => exact familySquareTrace_c1 hψ hθ hκ

/--
Defines `familyConstraintMap` of type `ι → ℝ` by `fun i => familyObservation hψ hθ hκ
(observations i) a-targets i`.

Use: `«2610.05164v2».Primal.exact_primal_family_of_contraction` rewrites with this definition
to establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 5.2 via `«2610.05164v2».Primal.familyConstraintMap_c1`.
-/
def familyConstraintMap {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ : ℝ} (hκ : 0<κ)
    (observations : ι → FamilyObservation) (targets : ι → ℝ) (a : ι → ℝ) : ι → ℝ :=
  fun i => familyObservation hψ hθ hκ (observations i) a-targets i

/--
Smoothness to the stated order: `ContDiff ℝ 1 (familyConstraintMap hψ hθ hκ observations
targets)`.

Use: `«2610.05164v2».Primal.exact_primal_family_of_contraction` uses this assertion to
establish the identity stated in that declaration.

Article: 2610.05164v2, Theorem 5.2.

Proof: Use the identities/estimates `«2610.05164v2».Primal.familyObservation_c1` with the
arguments shown in the proof.
-/
theorem familyConstraintMap_c1 {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ : ℝ} (hκ : 0<κ)
    (observations : ι → FamilyObservation) (targets : ι → ℝ) :
    ContDiff ℝ 1 (familyConstraintMap hψ hθ hκ observations targets) := by
  apply contDiff_pi.mpr
  intro i
  exact (familyObservation_c1 hψ hθ hκ (observations i)).sub contDiff_const

/--
Theorem 5.2's analytic implication, for any finite observation family. The Jacobian is `fderiv`
of the actual constraints, with no derivative oracle.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: 2610.05164v2, Theorem 5.2.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem exact_primal_family_of_contraction {ψ : ℝ → ℝ} {θ : ι → ℝ → ℝ}
    (hψ : Continuous ψ) (hθ : ∀ i,Continuous (θ i)) {κ : ℝ} (hκ : 0<κ)
    (observations : ι → FamilyObservation) (targets : ι → ℝ)
    (C : (ι → ℝ) →L[ℝ] (ι → ℝ)) {ρ ε : ℝ} {K : ℝ≥0}
    (hρ : 0≤ρ) (hK : K<1)
    (h0 : ‖C (familyConstraintMap hψ hθ hκ observations targets 0)‖≤ε)
    (hbound : ∀ a∈closedBall (0:ι → ℝ) ρ,
      ‖ContinuousLinearMap.id ℝ (ι → ℝ)-C.comp
        (fderiv ℝ (familyConstraintMap hψ hθ hκ observations targets) a)‖≤(K:ℝ))
    (hbudget : ε+(K:ℝ)*ρ≤ρ) :
    ∃ a∈closedBall (0:ι → ℝ) ρ,
      (∀ i,familyObservation hψ hθ hκ (observations i) a=targets i) ∧
      (∀ b∈closedBall (0:ι → ℝ) ρ,
        (∀ i,familyObservation hψ hθ hκ (observations i) b=targets i) → b=a) ∧
      Tendsto (fun n => (fun x => x-C (familyConstraintMap hψ hθ hκ observations targets x))^[n] 0)
        atTop (𝓝 a) ∧
      (∀ n : ℕ,(fun x => x-C (familyConstraintMap hψ hθ hκ observations targets x))^[n] 0∈
        closedBall (0:ι → ℝ) ρ ∧
        ‖(fun x => x-C (familyConstraintMap hψ hθ hκ observations targets x))^[n] 0-a‖≤
          (K:ℝ)^n*ε/(1-K)) ∧
      «2610.05164v2».GroundState.groundParameter
        ((speedData _ (affineProfile_continuous hψ hθ a)).density_integrable hκ)
        ((speedData _ (affineProfile_continuous hψ hθ a)).density_nonneg hκ)=κ ∧
      (∫ x,(speedData (affineProfile ψ θ a) (affineProfile_continuous hψ hθ a)).density κ x^(3/2:ℝ))≤
        exp (ρ*∑ i,‖unitDirection (hθ i)‖)*(∫ x,(speedData ψ hψ).density κ x^(3/2:ℝ)) := by
  -- Prove equality of functions by evaluating both sides at an arbitrary argument.
  let F := familyConstraintMap hψ hθ hκ observations targets
  have hF : Differentiable ℝ F :=
    (familyConstraintMap_c1 hψ hθ hκ observations targets).differentiable (by norm_num)
  obtain ⟨_,a,ha,hFa,ht,hu,he⟩ := chord_newton_matrix C (fderiv ℝ F) hρ hK h0
    (fun a _ => (hF a).hasFDerivAt) hbound hbudget
  have hzero (b : ι → ℝ) : F b=0 ↔ ∀ i,familyObservation hψ hθ hκ (observations i) b=targets i := by
    simp only [F,familyConstraintMap,funext_iff,Pi.zero_apply,sub_eq_zero]
  refine ⟨a,ha,(hzero a).mp hFa,fun b hb hh => hu b hb ((hzero b).mpr hh),ht,he,
    ground_exact (affineProfile_continuous hψ hθ a) hκ,?_⟩
  have ha' : ‖a‖≤ρ := by simpa using ha
  have hE : 0≤∫ x,(speedData ψ hψ).density κ x^(3/2:ℝ) :=
    integral_nonneg (fun x => Real.rpow_nonneg ((speedData ψ hψ).density_nonneg hκ x) _)
  exact (affine_family_energy_bound hψ hθ hκ a).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right ha' (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))) hE)

end
end «2610.05164v2».Primal
