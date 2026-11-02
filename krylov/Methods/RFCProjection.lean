import krylov.Methods.ProjectedResidual
import krylov.Methods.RFC
import krylov.Methods.ReferenceModels

/-!
Article: main_krylov, lem:projected-residual, application to actual gated RFC.
Use: bind the normalized residual estimates to the genuine retained history,
the computed conjugacy direction and the real observed correction execution.
Source: the existing data-only RFC policy and its exact finite model solve.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Adjoining the actual new probe adjoins its observed image to the finite image array.
Use: the latest-model estimates keep precisely the actual current probe.
Article: main_krylov, lem:projected-residual, augmented pair observations.
Proof: read the head and successor indices of the actual observed list. -/
theorem windowImages_cons (W : List (E × E)) (d z : E) :
    windowImages ((d,z)::W)=Fin.cons z (windowImages W) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- The actual RFC direction satisfies the genuine old-image conjugacy equations on its nonsingular solve domain.
Use: discharge the conjugacy premise in the normalized post-search residual estimate.
Article: main_krylov, lem:projected-residual, Yᵀd=0.
Proof: apply the previously proved conjugacy equation for the actual inverse coefficient solve. -/
theorem windowDirection_inner_zero (W : List (E × E)) (g : E)
    (hc : IsUnit (crossGram (windowImages W) (windowSteps W)).det) (i : Fin W.length) :
    inner ℝ (windowImages W i) (windowDirection W g)=0 :=
  congrFun (conjugacyDirection_conjugate _ _ g hc) i

/-- An accepted actual RFC correction gate executes precisely its actual latest-model correction.
Use: connect the physical normalized estimates to the genuine policy output and oracle gradient.
Article: main_krylov, alg:fc and lem:projected-residual.
Proof: unfold the accepted observed-data gate and its single real correction query. -/
theorem rfcCorrection_one_execution (memory : ℕ → ℕ) (H : History E)
    (z : E) (B : E →L[ℝ] E)
    (hgate : selectedWindow memory H≠[] ∧ ‖windowDefect (selectedWindow memory H)‖<1) :
    let W := selectedWindow memory H
    let d := windowDirection W H.gradient
    let U := (d,z)::W
    let g' := searchedGradient H.gradient d z
    let χ := combine (windowSteps U) (modelCoefficients (windowSteps U) (windowModel U) g')
    (runCorrections (rfcCorrection memory 1 H z) B g').movement=χ ∧
      (runCorrections (rfcCorrection memory 1 H z) B g').gradient=g'+B χ := by
  simp only [rfcCorrection]
  rw [ite_eq_left hgate]
  simp only [repeatedModelTree, runCorrections, add_zero, and_self]

/-- Every accepted actual repeated RFC phase obeys the normalized finite-query residual bound.
Use: the window, model, incoming gradient, gate and all subsequent right-hand sides are genuine policy data.
Article: main_krylov, lem:projected-residual, repeated RFC corrections.
Proof: identify the accepted actual decision tree with the implemented repeated
model tree and apply its proved physical normalization and finite residual bound. -/
theorem rfcCorrection_projected_bound (memory : ℕ → ℕ) (count : ℕ) (H : History E)
    (z : E) (B : E →L[ℝ] E)
    (hgate : selectedWindow memory H≠[] ∧ ‖windowDefect (selectedWindow memory H)‖<1)
    (hs : ∀ i, windowSteps ((windowDirection (selectedWindow memory H) H.gradient,z)::
      selectedWindow memory H) i≠0)
    (hmodel : IsUnit (rescaleModel
      (windowModel ((windowDirection (selectedWindow memory H) H.gradient,z)::selectedWindow memory H))
      (fun i => ‖windowSteps ((windowDirection (selectedWindow memory H) H.gradient,z)::
        selectedWindow memory H) i‖⁻¹)).det) :
    let W := selectedWindow memory H
    let d := windowDirection W H.gradient
    let U := (d,z)::W
    let g' := searchedGradient H.gradient d z
    let T := unitWindow (windowSteps U)
    let Hn := rescaleModel (windowModel U) (fun i => ‖windowSteps U i‖⁻¹)
    ‖projectedResidual T (runCorrections (rfcCorrection memory count H z) B g').gradient‖≤
      (‖correctionCompression T B-Hn‖*‖Hn⁻¹‖)^count*‖projectedResidual T g'‖ := by
  -- The gate is a condition on observed history; no correction is inserted into an unaccepted branch.
  simp only [rfcCorrection]
  rw [ite_eq_left hgate]
  exact repeatedModel_projected_bound _ _ _ (unitWindow_diagonal_unit _ hs) hmodel B _ count

/-- An actual RFC iteration with an empty retained window has exactly zero normalized current-direction residual after its real search.
Use: the initial and restarted empty-window cases are covered without inventing a correction query or an inverse model.
Article: main_krylov, lem:projected-residual, empty reference prefix.
Proof: the true empty-window gate chooses the real zero-correction phase;
the genuine exact search annihilates the current direction and its actual normalization. -/
theorem rfc_empty_window_projected_zero (memory : ℕ → ℕ) (count : ℕ)
    (H : History E) (A B : E →L[ℝ] E) (d : E)
    (hd : d=windowDirection (selectedWindow memory H) H.gradient)
    (hempty : selectedWindow memory H=[]) (hc : inner ℝ d (A d)≠0) :
    projectedResidual (fun _ : Fin 1 => ‖d‖⁻¹ • d)
      (methodAdvance (rfcMethod memory count) A B H).gradient=0 := by
  -- The actual iteration performs no correction query in this empty-window branch.
  have hdir : (rfcMethod memory count).direction H=d := hd.symm
  have hq : rfcCorrection memory count H (A d)=.done := by
    simp only [rfcCorrection,hempty,ne_eq,not_true_eq_false,false_and,ite_false]
  change projectedResidual _ (runCorrections (rfcCorrection memory count H
    (A ((rfcMethod memory count).direction H))) B (searchedGradient H.gradient
      ((rfcMethod memory count).direction H) (A ((rfcMethod memory count).direction H)))).gradient=0
  rw [hdir,hq]
  ext i
  change inner ℝ (‖d‖⁻¹ • d) (searchedGradient H.gradient d (A d))=0
  rw [real_inner_smul_left,searchedGradient_inner_zero _ _ _ hc,mul_zero]

/-- An actual empty-window RFC iteration also has exactly zero projection onto its genuine normalized newly recorded step.
Use: the initial and restarted recorded-window orders include the empty retained-window case, even if the line scalar vanishes.
Article: main_krylov, lem:projected-residual, initial recorded-step projection.
Proof: the real gate skips all corrections; the true recorded step is a scalar
multiple of the actual exactly searched direction, so both scalar normalizations preserve its zero pairing. -/
theorem rfc_empty_window_recorded_zero (memory : ℕ → ℕ) (count : ℕ)
    (H : History E) (A B : E →L[ℝ] E) (d : E)
    (hd : d=windowDirection (selectedWindow memory H) H.gradient)
    (hempty : selectedWindow memory H=[]) (hc : inner ℝ d (A d)≠0) :
    projectedResidual (fun _ : Fin 1 =>
      ‖lineLength H.gradient d (A d) • d‖⁻¹ • (lineLength H.gradient d (A d) • d))
      (methodAdvance (rfcMethod memory count) A B H).gradient=0 := by
  -- Only the real exact-search step is recorded, because the actual empty-window branch performs no correction.
  have hdir : (rfcMethod memory count).direction H=d := hd.symm
  have hq : rfcCorrection memory count H (A d)=.done := by
    simp only [rfcCorrection,hempty,ne_eq,not_true_eq_false,false_and,ite_false]
  change projectedResidual _ (runCorrections (rfcCorrection memory count H
    (A ((rfcMethod memory count).direction H))) B (searchedGradient H.gradient
      ((rfcMethod memory count).direction H) (A ((rfcMethod memory count).direction H)))).gradient=0
  rw [hdir,hq]
  ext i
  change inner ℝ (‖lineLength H.gradient d (A d) • d‖⁻¹ • (lineLength H.gradient d (A d) • d))
    (searchedGradient H.gradient d (A d))=0
  rw [real_inner_smul_left,real_inner_smul_left,searchedGradient_inner_zero _ _ _ hc,mul_zero,mul_zero]

end
end krylov.Methods
