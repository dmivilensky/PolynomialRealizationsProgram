import krylov.Correction.ReferenceSolve
import krylov.Methods.RepeatedModelQueries
import krylov.Stability.AnalyticMatrix

/-!
Article: main_krylov, thm:C2(b), actual fixed-model residual products.
Use: derive each actual inverse-model correction factor and propagate its
quadratic error through the genuinely observed repeated-query residual.
Source: the actual finite inverse is analytic at the proved reference unit;
the existing newest-factor-leftmost correction calculus supplies the product.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {p : ℕ}

/-- The actual inverse-model residual factor has its frozen-reference first-order factor with a quadratic error.
Use: no desired correction-product expansion is assumed when freezing the true inverse.
Article: main_krylov, thm:C2(b), N_pH⁻¹=L_pH₀⁻¹+O(ω²).
Proof: the true inverse is analytic and bounded at its proved reference
unit. Split the error as (N−L)H⁻¹+L(H⁻¹−H₀⁻¹); both actual products have
quadratic order by the existing spectral matrix product calculus. -/
theorem reference_matrix_factor_order (H N L : X → Matrix (Fin p) (Fin p) ℝ)
    (hH : AnalyticAt ℝ H 0) (hu : IsUnit (H 0).det)
    (hN : (fun z => N z-L z) =O[𝓝 (0 : X)] (fun z => ‖z‖^2))
    (hL : L =O[𝓝 (0 : X)] (fun z => ‖z‖)) :
    (fun z => N z*(H z)⁻¹-L z*(H 0)⁻¹) =O[𝓝 (0 : X)] (fun z => ‖z‖^2) := by
  -- Inverse regularity is used only on the actual nonsingular reference domain.
  have hi : AnalyticAt ℝ (fun z => (H z)⁻¹) 0 := analytic_spectral_matrix_inv H 0
    (fun i j => (((ContinuousLinearMap.proj (i,j)) ∘L
      (matrixEntryEquiv p p).toContinuousLinearMap).analyticAt _).comp hH)
    (isUnit_iff_ne_zero.mp hu)
  have hb := matrix_mul_bigO (fun z => N z-L z) (fun z => (H z)⁻¹)
    (fun z => ‖z‖^2) (fun _ => 1) hN (hi.continuousAt.tendsto.isBigO_one ℝ)
  have hc := matrix_mul_bigO L (fun z => (H z)⁻¹-(H 0)⁻¹)
    (fun z => ‖z‖) (fun z => ‖z‖) hL (analytic_reference_order _ hi)
  have hb' : (fun z => (N z-L z)*(H z)⁻¹) =O[𝓝 (0 : X)] (fun z => ‖z‖^2) := by
    simpa only [mul_one] using hb
  have hc' : (fun z => L z*((H z)⁻¹-(H 0)⁻¹)) =O[𝓝 (0 : X)] (fun z => ‖z‖^2) := by
    simpa only [← pow_two] using hc
  exact (hb'.add hc').congr_left fun z => by noncomm_ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual independently queried fixed-model corrections have the derived signed leading product and its full higher-order remainder.
Use: the actual newest-factor-leftmost product is applied to real updated query gradients, rather than a presumed residual recurrence.
Article: main_krylov, thm:C2(b), k_c-correction product remainder O(ω^(k_c+2)).
Proof: derive each actual inverse-model factor by the preceding theorem,
then apply the existing repeated-correction error calculus to the genuine
projected incoming vector. On the proved true inverse neighborhood, the
actual query-execution identity identifies that recurrence with the real
returned gradient, including independently varying correction segments. -/
theorem modelQueries_product_order (s : X → Fin p → E)
    (H : X → Matrix (Fin p) (Fin p) ℝ) (B : ℕ → X → E →L[ℝ] E)
    (g : X → E) (r : X → EuclideanSpace ℝ (Fin p))
    (L : ℕ → X → Matrix (Fin p) (Fin p) ℝ) (c : ℕ)
    (hH : AnalyticAt ℝ H 0) (hu : IsUnit (H 0).det)
    (hN : ∀ j<c, (fun z => correctionCompression (s z) (B j z)-H z-L j z) =O[𝓝 (0 : X)]
      (fun z => ‖z‖^2))
    (hL : ∀ j<c, L j =O[𝓝 (0 : X)] (fun z => ‖z‖))
    (hg : (fun z => projectedResidual (s z) (g z)-r z) =O[𝓝 (0 : X)] (fun z => ‖z‖^2))
    (hr : r =O[𝓝 (0 : X)] (fun z => ‖z‖)) :
    (fun z => projectedResidual (s z) (modelQueries (s z) (H z) (fun j => B j z) c (g z)).gradient-
      correctionRun (fun j z => Matrix.toEuclideanCLM (𝕜 := ℝ) (L j z*(H 0)⁻¹)) r c z) =O[𝓝 (0 : X)]
        (fun z => ‖z‖^(c+2)) := by
  -- Every leading factor is frozen only after deriving the actual inverse error to second order.
  let T := fun j z => Matrix.toEuclideanCLM (𝕜 := ℝ)
    ((correctionCompression (s z) (B j z)-H z)*(H z)⁻¹)
  let M := fun j z => Matrix.toEuclideanCLM (𝕜 := ℝ) (L j z*(H 0)⁻¹)
  have hT (j : ℕ) (hj : j<c) : (fun z => T j z-M j z) =O[𝓝 (0 : X)] (fun z => ‖z‖^2) := by
    simpa only [T,M,map_sub] using krylov.Secant.matrix_bigO_toEuclideanCLM _ _
      (reference_matrix_factor_order H (fun z => correctionCompression (s z) (B j z)-H z)
        (L j) hH hu (hN j hj) (hL j hj))
  have hM (j : ℕ) (hj : j<c) : M j =O[𝓝 (0 : X)] (fun z => ‖z‖) :=
    krylov.Secant.matrix_bigO_toEuclideanCLM _ _ (matrix_mul_const_bigO (L j) (H 0)⁻¹ _ (hL j hj))
  have he := repeated_correction_order T M (fun z => projectedResidual (s z) (g z)) r
    (fun z => ‖z‖) 1 c (by simpa only [norm_zero] using continuous_norm.tendsto (0 : X))
    hT hM hg (by simpa only [pow_one] using hr)
  have hunit : ∀ᶠ z in 𝓝 (0 : X), IsUnit (H z).det :=
    ((continuous_id.matrix_det.continuousAt.comp hH.continuousAt).eventually_ne
      (isUnit_iff_ne_zero.mp hu)).mono fun _ hz => isUnit_iff_ne_zero.mpr hz
  apply (he.congr_right fun z => by congr 1; omega).congr' ?_ (EventuallyEq.refl _ _)
  filter_upwards [hunit] with z hz
  rw [modelQueries_projected s H B g z hz]

end
end krylov.Correction
