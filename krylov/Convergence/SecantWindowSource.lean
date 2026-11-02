import krylov.Convergence.WindowModelBounds
import krylov.Convergence.SecantSourceBounds

/-!
Article: main_krylov, thm:Ip, actual SS1 source-to-model convergence.
Use: derive superlinear error reduction from genuine local derivatives and
uniformly independent observed windows. In particular, convergence of the
model or a desired error recurrence is never a source hypothesis.
Source: the actual secant FTC bounds, observed normalization, and continuity
of inversion at the identity.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Filter Topology Asymptotics Set krylov.Methods krylov.Secant
  krylov.Reference krylov.LinearAlgebra chebyshev1.Nonlinear
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator NNReal
variable {n : ℕ} {α : Type*} {l : Filter α}

/-- The real Euclidean matrix of a genuine derivative. -/
def secantMatrix (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ := (Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ)).symm A

theorem secantMatrix_operator
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    cgOperator (secantMatrix A)=A :=
  (Matrix.toEuclideanCLM (n:=Fin n) (𝕜:=ℝ)).apply_symm_apply A

theorem secantMatrix_norm
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ‖secantMatrix A‖=‖A‖ := by
  rw [←Matrix.l2_opNorm_toEuclideanCLM]
  exact congrArg norm (secantMatrix_operator A)

theorem secantMatrix_sub_one
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ‖secantMatrix A-1‖=‖A-ContinuousLinearMap.id ℝ _‖ := by
  rw [←Matrix.l2_opNorm_toEuclideanCLM,map_sub,map_one]
  exact congrArg (fun B=>‖B-ContinuousLinearMap.id ℝ _‖) (secantMatrix_operator A)

/-- A nonsingular actual column matrix excludes every zero observed step. -/
theorem windowMatrix_step_ne_zero (s : Fin n → EuclideanSpace ℝ (Fin n))
    (hs : IsUnit (windowMatrix s).det) (i : Fin n) : s i≠0 := by
  have hi := Matrix.linearIndependent_cols_of_det_ne_zero (isUnit_iff_ne_zero.mp hs)
  intro hz
  apply hi.ne_zero i
  funext a
  change s i a=0
  rw [hz]
  rfl

/-- The genuine source budget for a finite observed window. -/
def sourceWindowRadius {E : Type*} [NormedAddCommGroup E]
    (a b : Fin n → E) : ℝ := ∑ i, (‖a i‖+‖b i‖)

theorem sourceWindowRadius_nonneg {E : Type*} [NormedAddCommGroup E]
    (a b : Fin n → E) : 0≤sourceWindowRadius a b :=
  Finset.sum_nonneg fun i _=>add_nonneg (norm_nonneg (a i)) (norm_nonneg (b i))

/-- Uniform errors for the actual normalized images follow from genuine local
Hessian regularity, with no model or secant approximation premise. -/
theorem source_unit_window_error
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : Convex ℝ S) (h₀ : (0:EuclideanSpace ℝ (Fin n))∈S)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S, HasFDerivAt G (H z) z)
    (a b : Fin n → EuclideanSpace ℝ (Fin n)) (ha : ∀ i,a i∈S) (hb : ∀ i,b i∈S)
    (hs : ∀ i,b i-a i≠0) (i : Fin n) :
    ‖unitWindowImages (fun j=>b j-a j) (fun j=>G (b j)-G (a j)) i-
      unitWindow (fun j=>b j-a j) i‖≤(L:ℝ)/2*sourceWindowRadius a b := by
  apply unitWindow_image_error _ _ hs
  intro j
  have hh := secant_image_endpoint_bound G H S hS h₀ hH hG (a j) (b j) (ha j) (hb j)
  rw [hH₀,ContinuousLinearMap.id_apply] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.single_le_sum (fun i _=>add_nonneg (norm_nonneg (a i)) (norm_nonneg (b i)))
    (Finset.mem_univ j)

/-- Actual independent windows of a genuine convergent local source give
superlinear SS1 queries. The finite window can move arbitrarily with the
filter; only the stated uniform inverse-coordinate bound is required.
Article: main_krylov, thm:Ip, superlinearity before oldest-pair refinement. -/
theorem ss1_source_superlinear
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) {L : ℝ≥0}
    (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S, HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (a b : α → Fin (n+1) → EuclideanSpace ℝ (Fin (n+1)))
    (x : α → EuclideanSpace ℝ (Fin (n+1)))
    (ha : ∀ i,Tendsto (fun z=>a z i) l (𝓝 0))
    (hb : ∀ i,Tendsto (fun z=>b z i) l (𝓝 0)) (hx : Tendsto x l (𝓝 0))
    (hmem : ∀ᶠ z in l, (∀ i,a z i∈S) ∧ (∀ i,b z i∈S) ∧ x z∈S)
    {C : ℝ} (hC : 0≤C)
    (hind : ∀ᶠ z in l,
      IsUnit (windowMatrix (unitWindow (fun i=>b z i-a z i))).det ∧
      ‖(windowMatrix (unitWindow (fun i=>b z i-a z i)))⁻¹‖≤C) :
    (fun z=>ss1Point (fun i=>b z i-a z i) (fun i=>G (b z i)-G (a z i)) (G (x z)) (x z))
      =o[l] (fun z=>‖x z‖) := by
  let s := fun z i=>b z i-a z i
  let y := fun z i=>G (b z i)-G (a z i)
  let V := fun z=>windowMatrix (unitWindow (s z))
  let X := fun z=>windowDataError (unitWindow (s z)) (unitWindowImages (s z) (y z))
  let A := fun z=>secantMatrix (averagedDerivative H 0 (x z))
  let ε := fun z=>(L:ℝ)/2*sourceWindowRadius (a z) (b z)
  have hε : Tendsto ε l (𝓝 0) := by
    have hr : Tendsto (fun z=>sourceWindowRadius (a z) (b z)) l (𝓝 0) := by
      have ht := tendsto_finsetSum Finset.univ (fun i _=>(ha i).norm.add (hb i).norm)
      simpa only [norm_zero,add_zero,Finset.sum_const_zero,sourceWindowRadius] using ht
    simpa only [mul_zero] using hr.const_mul ((L:ℝ)/2)
  have hs : ∀ᶠ z in l,∀ i,s z i≠0 := by
    filter_upwards [hind] with z hz i
    intro hi
    have hh := windowMatrix_step_ne_zero (unitWindow (s z)) hz.1 i
    apply hh
    simp only [unitWindow,rescaleWindow,hi,smul_zero]
  have hX : Tendsto X l (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [hmem,hs] with z hz hsz
      exact windowDataError_norm _ _ (unitWindow_norm _ hsz)
        (mul_nonneg (by positivity) (sourceWindowRadius_nonneg _ _))
        (source_unit_window_error G H S hS h₀ hH hH₀ hG _ _ hz.1 hz.2.1 hsz)
    · simpa only [mul_zero,Nat.cast_add,Nat.cast_one,ε] using hε.const_mul (n+1:ℝ)
  have hA : Tendsto A l (𝓝 1) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (g:=fun z=>(L:ℝ)/2*‖x z‖)
    · exact Filter.Eventually.of_forall fun z=>norm_nonneg (A z-1)
    · filter_upwards [hmem] with z hz
      rw [show ‖A z-1‖=‖averagedDerivative H 0 (x z)-ContinuousLinearMap.id ℝ _‖ from
        secantMatrix_sub_one _]
      have hh := secant_operator_endpoint_bound H S hS h₀ hH 0 (x z) h₀ hz.2.2
      simpa only [hH₀,norm_zero,zero_add,sub_zero] using hh
    · simpa only [norm_zero,mul_zero] using hx.norm.const_mul ((L:ℝ)/2)
  have hh := conditioned_model_convergence V X A x hC (hind.mono fun _ h=>h.2) hX hA
  apply hh.2.2.2.2.congr'
  · filter_upwards [hind,hs,hmem] with z hz hsz hzm
    have hdiag := unitWindow_diagonal_unit (s z) hsz
    have hpoint := ss1Point_rescale (s z) (y z) (fun i=>‖s z i‖⁻¹) hdiag (G (x z)) (x z)
    have hmodel := window_model_error (unitWindow (s z)) (unitWindowImages (s z) (y z)) hz.1
    have hj : inverseCongruence (V z) (ss1Model (unitWindow (s z)) (unitWindowImages (s z) (y z)))=
        1+inverseCongruence (V z) (X z) := by
      change _-1=inverseCongruence (V z) (X z) at hmodel
      rw [←hmodel]
      abel
    have hrad : cgOperator (A z) (x z)=G (x z) := by
      rw [secantMatrix_operator]
      have hp t (ht : t∈Icc (0:ℝ) 1) : (0:EuclideanSpace ℝ (Fin (n+1)))+t • x z∈S :=
        hS.add_smul_mem h₀ (by simpa only [zero_add] using hzm.2.2) ht
      have hc := hH.continuousOn.comp
        (continuous_const.add (continuous_id.smul continuous_const)).continuousOn hp
      simpa only [zero_add,hG₀,sub_zero] using
        averagedDerivative_apply G H 0 (x z) hc (fun t ht=>hG _ (hp t ht))
    rw [←hpoint]
    change WithLp.toLp 2 (WithLp.ofLp (x z)-
      (1+inverseCongruence (V z) (X z))⁻¹*ᵥ(A z*ᵥWithLp.ofLp (x z)))=
      ss1Point (unitWindow (s z)) (unitWindowImages (s z) (y z)) (G (x z)) (x z)
    rw [ss1Point_eq_model_step _ _ _ _ hz.1,hj]
    rw [←hrad]
    rfl
  · exact Filter.EventuallyEq.refl _ _

end
end krylov.Convergence
