import krylov.Cancellation.DCPhysicalWindow
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs(b,c), genuine executed Gauss--Radau DC reference.
Use: derive positive actual estimates and the full original one-gradient
quadratic trajectory for the implemented observed arithmetic policy itself.
Source: actual DC quadratic flag induction, genuine native curvature inputs
and the proved real physical window feasibility/minimax dictionary.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Reference
variable {n : ℕ}

/-- The original observed arithmetic policy selects positive estimates on
every actual full-memory one-gradient nonstagnating positive quadratic prefix.
Use: the genuine implementation discharges its own reference estimate domain,
rather than assuming positive trials independently of its observed-data rule.
Article: main_krylov, thm:dcs(b,c).
Proof: induct on the actual queried prefix. Earlier proved positive estimates
supply the genuine independent full CG flag and true virtual inputs. The
real positive incoming factor makes the original observed descent pairing
positive. True quadratic secants and physical spectral feasibility then give
a positive original arithmetic estimate on the actual next history. -/
theorem dc_gauss_radau_one_gradient_positive
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (mu L : ℝ) (hmu : 0<mu) (hmuL : mu≤L)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (L • 1-base).PosSemidef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ k<N,CG.gradient (cgOperator base) g k≠0) :
    ∀ k<N,0<dcGaussRadauEstimate fullMemory mu L (oneGradientRun
      (dcSlideOneGradient fullMemory (dcGaussRadauEstimate fullMemory mu L)) (fun _ => cgOperator base) g k) := by
  let Q := cgOperator base
  let estimate := dcGaussRadauEstimate fullMemory mu L (n := n)
  let m := dcSlideOneGradient fullMemory estimate
  have hQ := (cgOperator_positive base hb).1
  have hpos := (cgOperator_positive base hb).2
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    have ht : ∀ j<k,0<estimate (oneGradientRun m (fun _ => Q) g j) :=
      fun j hj => ih j hj (hj.trans hk)
    have hprefix : ∀ j<k,CG.gradient Q g j≠0 := fun j hj => hpre j (hj.trans hk)
    have hstate := dc_one_gradient_state estimate Q hQ hpos g k hprefix ht k le_rfl
    have hinputs := dc_one_gradient_curvature_inputs estimate Q hQ hpos g k hprefix ht k le_rfl
    let H := oneGradientRun m (fun _ => Q) g k
    have hInv := CG.invariant Q hQ hpos g k hprefix
    have hq : 0<dcCurvatureSlope fullMemory H := by
      have he : dcCurvatureSlope fullMemory H=
          dcIncomingFactor estimate Q g k*‖CG.gradient Q g k‖^2 := by
        have hp : inner ℝ (CG.gradient Q g k) (CG.direction Q g k)= -‖CG.gradient Q g k‖^2 :=
          (real_inner_comm _ _).trans hInv.search_pair
        unfold dcCurvatureSlope
        rw [hinputs.1,hinputs.2,real_inner_smul_right,hp]
        ring
      rw [he]
      exact mul_pos hstate.1 (sq_pos_of_pos (norm_pos_iff.mpr (hpre k hk)))
    have hy : ∀ j,windowImages (selectedWindow fullMemory H) j=
        Q (windowSteps (selectedWindow fullMemory H) j) := by
      rw [selectedWindow_full]
      exact fun j => oneGradientRun_pairs_quadratic m Q g k (H.pairs.get j) (List.get_mem _ j)
    have hLI : LinearIndependent ℝ (windowSteps (selectedWindow fullMemory H)) := by
      rw [selectedWindow_full]
      exact hstate.2.1
    exact (dc_quadratic_gauss_radau_bound fullMemory H base hb mu L hmu hmuL hlo hhi hy hLI hq).1

/-- The actual original arithmetic-curvature one-gradient DC implementation
has its complete positive CG-line trajectory and old-flag orthogonality,
with all trial, native inverse and physical completion domains discharged.
Use: the source algorithm is executed from its one observed-data estimate
rule on every true positive nonstagnating quadratic prefix.
Article: main_krylov, thm:dcs(b), actual Gauss--Radau implementation.
Proof: the preceding real execution induction proves positivity of every
chosen observed estimate. Insert those genuine implemented reference domains
into the proved full native DC quadratic trajectory theorem. -/
theorem dc_gauss_radau_one_gradient_trajectory
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (mu L : ℝ) (hmu : 0<mu) (hmuL : mu≤L)
    (hlo : (base-mu • 1).PosSemidef) (hhi : (L • 1-base).PosSemidef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hpre : ∀ j<N,CG.gradient (cgOperator base) g j≠0)
    (k : ℕ) (hk : k<N) :
    let estimate := dcGaussRadauEstimate fullMemory mu L (n := n)
    let Q := cgOperator base
    let m := dcSlideOneGradient fullMemory estimate
    0<dcEvaluatedLength estimate Q g k ∧
      (oneGradientRun m (fun _ => Q) g (k+1)).displacement=
        CG.displacement Q g k+dcEvaluatedLength estimate Q g k • CG.direction Q g k ∧
      ∀ v∈directionFlag Q g k,inner ℝ v (oneGradientRun m (fun _ => Q) g (k+1)).gradient=0 :=
  dc_one_gradient_evaluated _ _ (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 g N hpre
    (dc_gauss_radau_one_gradient_positive base hb mu L hmu hmuL hlo hhi g N hpre) k hk

end
end krylov.Cancellation
