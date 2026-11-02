import krylov.Methods.PairSolveOrder
import krylov.Secant.LatestCongruenceOrder
import krylov.Stability.ContDiffSpectralMatrix
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), actual virtual pair-change comparison.
Use: compare real virtual gradients under a common observed pair change,
with the latest model's quadratic congruence error derived, not assumed.
Source: exact physical pair dictionaries, true spectral inverse comparison
and the proved first-order latest-model congruence theorem.
-/

namespace krylov.Methods
noncomputable section
open Matrix Filter Topology Asymptotics krylov.LinearAlgebra krylov.Stability krylov.Secant
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] {p : ℕ}

/-- The actual finite virtual gradient of an observed pair model.
Use: compare actual S fields and true native D fields on the same history.
Article: main_krylov, thm:local(a), real virtual model solve. -/
def pairVirtualGradient (s y : Fin p → E) (v : E) : E :=
  v+combine y (modelCoefficients s (pairModel s y) v)

/-- A common actual pair change exposes its inverse model action exactly.
Use: real virtual-gradient differences reduce to actual spectral matrices.
Article: main_krylov, thm:local(a), exact changed virtual solve.
Proof: the actual right-hand side and physical synthesis each transform
by the true column matrix, including the computed negative coefficients. -/
theorem pairVirtualGradient_rightChange (s y : Fin p → E)
    (T : Matrix (Fin p) (Fin p) ℝ) (v : E) :
    pairVirtualGradient (rightChange s T) (rightChange y T) v=
      v-combine y ((T*(latest (Tᵀ*crossGram y s*T))⁻¹*Tᵀ) *ᵥ coordinates s v) := by
  simp only [pairVirtualGradient,pairModel_eq_latest,crossGram_rightChange,modelCoefficients,
    coordinates_rightChange,combine_rightChange,Matrix.mulVec_neg,Matrix.mulVec_mulVec]
  simp only [combine,Pi.neg_apply,neg_smul,Finset.sum_neg_distrib,sub_eq_add_neg,Matrix.mul_assoc]

/-- Actual finite virtual gradients change only quadratically under a
C-one common pair change whose true reference is diagonal and whose
reference pairings are symmetric and nonsingular. Every model-order and
inverse-domain hypothesis is derived from these primitive actual fields.
Use: the genuine informed S policy on a D history uses the same virtual
fields to first order, with no assumed off-quadratic field equality.
Article: main_krylov, thm:local(a), genuine native virtual comparison.
Proof: the true latest selector has a quadratic congruence defect. The
existing inverse comparison transports it to the actual inverse action.
Its true observed right-hand side and image columns are bounded. Exact
finite solve algebra identifies their synthesized error with the genuine
changed virtual gradient minus the original virtual gradient. -/
theorem pairVirtualGradient_change_quadratic
    (s y : X → Fin p → E) (v : X → E) (T : X → Matrix (Fin p) (Fin p) ℝ)
    (hs : ∀ i,ContDiffAt ℝ 1 (fun z => s z i) 0)
    (hy : ∀ i,ContDiffAt ℝ 1 (fun z => y z i) 0) (hv : ContDiffAt ℝ 1 v 0)
    (hT : ContDiffAt ℝ 1 T 0) (d : Fin p → ℝ) (hT0 : T 0=diagonal d)
    (hu : IsUnit (T 0).det) (hC0 : (crossGram (y 0) (s 0)).IsSymm)
    (hM0 : IsUnit (pairModel (s 0) (y 0)).det) :
    (fun z => pairVirtualGradient (rightChange (s z) (T z)) (rightChange (y z) (T z)) (v z)-
      pairVirtualGradient (s z) (y z) (v z)) =O[𝓝 0] (fun z => ‖z‖^2) := by
  let C := fun z => crossGram (y z) (s z)
  let M := fun z => latest (C z)
  let H := fun z => latest ((T z)ᵀ*C z*T z)
  have hC : ContDiffAt ℝ 1 C 0 := contDiff_spectral_matrix _ _ (fun i j => (hy i).inner ℝ (hs j))
  have hM : ContDiffAt ℝ 1 M 0 := contDiff_spectral_matrix _ _
    (fun i j => (hy (min i j)).inner ℝ (hs (max i j)))
  have hH : ContDiffAt ℝ 1 H 0 := by
    have hc : ContDiffAt ℝ 1 (fun z => (T z)ᵀ*C z*T z) 0 :=
      ((contDiff_spectral_matrix _ _ (fun i j => contDiffAt_pi.mp ((matrixEntryEquiv p p).toContinuousLinearMap.contDiff.contDiffAt.comp 0 hT) (j,i))).mul hC).mul hT
    exact contDiff_spectral_matrix _ _ (fun i j => contDiffAt_pi.mp ((matrixEntryEquiv p p).toContinuousLinearMap.contDiff.contDiffAt.comp 0 hc) (min i j,max i j))
  have hdiff : (fun z => (T z)ᵀ*M z*T z-H z) =O[𝓝 0] (fun z => ‖z‖^2) :=
    (latest_congruence_quadratic C T hC hT hC0 d hT0).neg_left.congr_left
      (fun z => neg_sub _ _)
  have hH0 : H 0=(T 0)ᵀ*M 0*T 0 := by
    dsimp only [H,M]
    rw [hT0,Matrix.diagonal_transpose,latest_diagonal_congruence]
  have hHunit : IsUnit (H 0).det := by
    rw [hH0,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose]
    exact (hu.mul (by simpa only [M,pairModel_eq_latest] using hM0)).mul hu
  have hpow : Tendsto (fun z : X => ‖z‖^2) (𝓝 0) (𝓝 0) := by
    have hn : Tendsto (fun z : X => ‖z‖) (𝓝 0) (𝓝 0) := by
      simpa only [norm_zero] using continuous_norm.tendsto (0 : X)
    simpa only [zero_pow (by norm_num : (2 : ℕ)≠0)] using hn.pow 2
  have hi := full_basis_inverse_order T M H (T 0) (H 0) hu hHunit _ hpow
    hT.continuousAt.tendsto hH.continuousAt.tendsto hdiff
  have hyb (i : Fin p) : (fun z => y z i) =O[𝓝 0] (fun _ => (1 : ℝ)) :=
    (hy i).continuousAt.tendsto.isBigO_one ℝ
  have hcoord (i : Fin p) : (fun z => coordinates (s z) (v z) i) =O[𝓝 0] (fun _ => (1 : ℝ)) :=
    ((hs i).inner ℝ hv).continuousAt.tendsto.isBigO_one ℝ
  have hc (i : Fin p) : (fun z => (((M z)⁻¹-T z*(H z)⁻¹*(T z)ᵀ) *ᵥ coordinates (s z) (v z)) i)
      =O[𝓝 0] (fun z => ‖z‖^2) := by
    simpa only [mul_one] using matrix_mulVec_order _ _ _ _ hi hcoord i
  have hout : (fun z => combine (y z) (((M z)⁻¹-T z*(H z)⁻¹*(T z)ᵀ) *ᵥ coordinates (s z) (v z)))
      =O[𝓝 0] (fun z => ‖z‖^2) := by simpa only [mul_one] using combine_order y _ _ _ hyb hc
  apply hout.congr_left
  intro z
  rw [pairVirtualGradient_rightChange]
  dsimp only [pairVirtualGradient,modelCoefficients]
  rw [Matrix.sub_mulVec]
  simp only [M,H,C,pairModel_eq_latest,combine,Pi.sub_apply,Pi.neg_apply,sub_smul,neg_smul,
    Finset.sum_sub_distrib,Finset.sum_neg_distrib]
  abel

end
end krylov.Methods
