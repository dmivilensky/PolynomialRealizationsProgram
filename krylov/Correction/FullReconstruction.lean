import krylov.Correction.NativeExpansion
import krylov.Stability.ObliqueResponse

/-!
Article: main_krylov, thm:C, reconstruction of the actual full terminal gradient.
Use: remove the moving full projection from the native second-order RFC
expansion with a proved cubic cost, using the actual nonsingular reference basis.
Source: the existing exact column-pairing identity, genuine finite Euclidean
linear independence, analytic inversion and asymptotic operator-action calculus.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {p : ℕ}

/-- The actual square physical column matrix of a full Euclidean model family.
Use: its transpose is the real projected-residual map of the actual correction window.
Article: main_krylov, thm:C, physical full basis U. -/
def fullBasisMatrix (u : Fin p → EuclideanSpace ℝ (Fin p)) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun i j => u j i

/-- Projection onto a full actual family is exactly the transpose action of its physical matrix.
Use: reconstruct actual gradients without assuming an orthonormal moving window.
Article: main_krylov, thm:C, Uᵀg as a genuine Euclidean vector.
Proof: use the existing exact real pairing with each true physical matrix column. -/
theorem projectedResidual_fullBasisMatrix (u : Fin p → EuclideanSpace ℝ (Fin p))
    (g : EuclideanSpace ℝ (Fin p)) :
    projectedResidual u g=Matrix.toEuclideanCLM (𝕜 := ℝ) (fullBasisMatrix u)ᵀ g := by
  ext i
  exact column_inner_eq_coordinate (fullBasisMatrix u) i g

/-- An actually independent full Euclidean family has a genuinely nonsingular physical column matrix.
Use: derive the reference reconstruction domain from the genuine CG family.
Article: main_krylov, thm:C, nondegenerate full reference basis.
Proof: the true Euclidean coordinate equivalence preserves linear independence;
the existing square-matrix column criterion then proves the determinant is a unit. -/
theorem fullBasisMatrix_unit (u : Fin p → EuclideanSpace ℝ (Fin p))
    (hu : LinearIndependent ℝ u) : IsUnit (fullBasisMatrix u).det := by
  let e := WithLp.linearEquiv 2 ℝ (Fin p → ℝ)
  have hc : LinearIndependent ℝ (fullBasisMatrix u).col := by
    change LinearIndependent ℝ (e ∘ u)
    exact hu.map' e.toLinearMap e.ker
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_cols_iff_isUnit.mp hc)

/-- A genuine higher-order projected expansion reconstructs the physical vector with the inverse reference transpose.
Use: freezing the actual moving reconstruction costs one extra order beyond
the projected leading coefficient.
Article: main_krylov, thm:C2(b), full-basis reconstruction at every correction order.
Proof: the actual transpose inverse is analytic and locally bounded. Apply it
to the true higher-order projected remainder; its first-order difference from the
reference inverse multiplies only the higher-order leading coefficient. -/
theorem full_projection_reconstruction_order_at
    (R : X → Matrix (Fin p) (Fin p) ℝ) (g c : X → EuclideanSpace ℝ (Fin p)) (order : ℕ)
    (hR : ∀ i j, AnalyticAt ℝ (fun z => R z i j) 0) (hu : IsUnit (R 0).det)
    (hc : c =O[𝓝 (0 : X)] (fun z => ‖z‖^order))
    (hproj : (fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (R z)ᵀ (g z)+c z) =O[𝓝 (0 : X)]
      (fun z => ‖z‖^(order+1))) :
    (fun z => g z+Matrix.toEuclideanCLM (𝕜 := ℝ) ((R 0)ᵀ)⁻¹ (c z)) =O[𝓝 (0 : X)]
      (fun z => ‖z‖^(order+1)) := by
  -- Only the reconstruction changes: its first-order error multiplies the leading coefficient.
  let D := fun z => ((R z)ᵀ)⁻¹
  let Dc := fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (D z)
  have hut : IsUnit ((R 0)ᵀ).det := by simpa only [det_transpose] using hu
  have hD : AnalyticAt ℝ D 0 := analytic_spectral_matrix_inv _ 0 (fun i j => hR j i)
    (isUnit_iff_ne_zero.mp hut)
  have hDb : Dc =O[𝓝 (0 : X)] (fun _ => (1 : ℝ)) :=
    krylov.Secant.matrix_bigO_toEuclideanCLM D _ (hD.continuousAt.tendsto.isBigO_one ℝ)
  have hDd : (fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (D 0)-Dc z) =O[𝓝 (0 : X)] (fun z => ‖z‖) := by
    have hr := krylov.Secant.matrix_bigO_toEuclideanCLM (fun z => D z-D 0) _ (analytic_reference_order D hD)
    simp only [map_sub] at hr
    simpa only [neg_sub] using hr.neg_left
  have h₁ := operator_action_order Dc
    (fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (R z)ᵀ (g z)+c z) (fun _ => 1)
    (fun z => ‖z‖^(order+1)) hDb hproj
  have h₂ := operator_action_order (fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (D 0)-Dc z)
    c (fun z => ‖z‖) (fun z => ‖z‖^order) hDd hc
  have h₁' : (fun z => Dc z (Matrix.toEuclideanCLM (𝕜 := ℝ) (R z)ᵀ (g z)+c z)) =O[𝓝 (0 : X)]
      (fun z => ‖z‖^(order+1)) := by simpa only [one_mul] using h₁
  have h₂' : (fun z => (Matrix.toEuclideanCLM (𝕜 := ℝ) (D 0)-Dc z) (c z)) =O[𝓝 (0 : X)]
      (fun z => ‖z‖^(order+1)) := by simpa only [← pow_succ'] using h₂
  have hdet := analytic_matrix_det R 0 hR
  have hunit : ∀ᶠ z in 𝓝 (0 : X), IsUnit (R z).det :=
    (hdet.continuousAt.eventually_ne (isUnit_iff_ne_zero.mp hu)).mono fun _ hz => isUnit_iff_ne_zero.mpr hz
  apply (h₁'.add h₂').congr' ?_ (Filter.EventuallyEq.refl _ _)
  filter_upwards [hunit] with z hz
  have he : Dc z (Matrix.toEuclideanCLM (𝕜 := ℝ) (R z)ᵀ (g z))=g z := by
    change Matrix.toEuclideanCLM (𝕜 := ℝ) (D z) (Matrix.toEuclideanCLM (𝕜 := ℝ) (R z)ᵀ (g z))=g z
    rw [← mul_apply_eq_comp,← map_mul,nonsing_inv_mul _ (by simpa only [det_transpose] using hz),map_one,one_apply_eq_self]
  simp only [map_add,_root_.sub_apply,he]
  dsimp only [D]
  abel

/-- A genuine cubic projected expansion reconstructs the physical vector with the inverse reference transpose.
Use: freezing the actual moving reconstruction costs cubic order because its
projected vector already has quadratic order.
Article: main_krylov, thm:C, full-basis reconstruction of the second-order residual.
Proof: the actual transpose inverse is analytic and locally bounded. Apply it
to the true cubic projected remainder; its first-order difference from the
reference inverse multiplies only a quadratic leading coefficient. -/
theorem full_projection_reconstruction_order
    (R : X → Matrix (Fin p) (Fin p) ℝ) (g c : X → EuclideanSpace ℝ (Fin p))
    (hR : ∀ i j, AnalyticAt ℝ (fun z => R z i j) 0) (hu : IsUnit (R 0).det)
    (hc : c =O[𝓝 (0 : X)] (fun z => ‖z‖^2))
    (hproj : (fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (R z)ᵀ (g z)+c z) =O[𝓝 (0 : X)]
      (fun z => ‖z‖^3)) :
    (fun z => g z+Matrix.toEuclideanCLM (𝕜 := ℝ) ((R 0)ᵀ)⁻¹ (c z)) =O[𝓝 (0 : X)]
      (fun z => ‖z‖^3) := by
  exact full_projection_reconstruction_order_at R g c 2 hR hu hc hproj

/-- The actual full terminal RFC gradient has its native physical second-order coefficient and cubic remainder.
Use: remove the last projected window from the genuine executed expansion;
the full reference basis is proved nonsingular from true CG nonstagnation.
Article: main_krylov, thm:C, physical second-order residual before canonical flag simplification.
Proof: the actual projected expansion and quadratic leading coefficient are
already derived. The genuine full CG step/direction family is independent,
so its real column matrix gives the reference inverse transpose. Apply the
proved reconstruction estimate to the actual output gradient. -/
theorem full_physical_second_order {k : ℕ}
    (A B : X → ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (g : X → EuclideanSpace ℝ (Fin (k+1)))
    (hA : ∀ i, AnalyticAt ℝ (fun z => A z i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun z => B z i) 0) (hg : AnalyticAt ℝ g 0)
    (hAsym : ∀ z i, (A z i).toLinearMap.IsSymmetric)
    (Q : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hA0 : A 0=(fun _ => Q)) (hB0 : B 0=(fun _ => Q))
    (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : EuclideanSpace ℝ (Fin (k+1)), v≠0 → 0 < inner ℝ v (Q v))
    (hk : 0<k) (hpre : ∀ i≤k, CG.gradient Q (g 0) i≠0) :
    let m := rfcMethod fullMemory 1
    let U := fun z => probedStepBasis m (A z) (B z) (g z) k
    let H := fun z => pairModel (U z) (probedImageBasis m (A z) (B z) (g z) k)
    let L := fun z => Matrix.of fun i j =>
      inner ℝ (U 0 i) ((B z k-A z (k-(min i j).val)) (U 0 j))
    let R₀ := fullBasisMatrix (U 0)
    (fun z => probedGradient m (A z) (B z) (g z) (k+1)+
      Matrix.toEuclideanCLM (𝕜 := ℝ) (R₀ᵀ⁻¹*(L z*(H 0)⁻¹))
        (frozenIncoming Q (g 0) (A z) k)) =O[𝓝 (0 : X)] (fun z => ‖z‖^3) := by
  -- The full reference inverse is derived from actual globally CG-consistent execution.
  let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin (k+1)))
  let U := fun z => probedStepBasis m (A z) (B z) (g z) k
  let H := fun z => pairModel (U z) (probedImageBasis m (A z) (B z) (g z) k)
  let L := fun z => Matrix.of fun i j => inner ℝ (U 0 i)
    ((B z k-A z (k-(min i j).val)) (U 0 j))
  let R := fun z => fullBasisMatrix (U z)
  let c := fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (L z*(H 0)⁻¹) (frozenIncoming Q (g 0) (A z) k)
  have hd := full_cycle_data_regular 1 A B g hA hB hg Q hA0 hB0 hQ hpos k hpre
  have hR (i j : Fin (k+1)) : AnalyticAt ℝ (fun z => R z i j) 0 :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k+1) => ℝ) i).analyticAt _).comp (hd.2.1 j)
  have hU : LinearIndependent ℝ (U 0) := by
    dsimp only [U]
    rw [hA0,hB0]
    exact probedStepBasis_independent m (rfcMethod_consistent fullMemory (fun _ ha => ha) 1)
      Q hQ hpos (g 0) k hpre
  have hu : IsUnit (R 0).det := fullBasisMatrix_unit _ hU
  have hLa : AnalyticAt ℝ L 0 := analytic_spectral_matrix L 0 fun i j =>
    analytic_inner analyticAt_const
      (analytic_operator_apply ((hB k).sub (hA (k-(min i j).val))) analyticAt_const)
  have hL₀ : L 0=0 := by
    ext i j
    simp only [L,hA0,hB0,sub_self,_root_.zero_apply,inner_zero_right,Matrix.of_apply,Matrix.zero_apply]
  have hL : L =O[𝓝 (0 : X)] (fun z => ‖z‖) := by
    simpa only [hL₀,sub_zero] using analytic_reference_order L hLa
  have hc : c =O[𝓝 (0 : X)] (fun z => ‖z‖^2) := by
    have hM := krylov.Secant.matrix_bigO_toEuclideanCLM _ _ (matrix_mul_const_bigO L (H 0)⁻¹ _ hL)
    simpa only [← pow_two] using operator_action_order _ _ _ _ hM (frozenIncoming_order A hA Q hA0 (g 0) k)
  have hnative := full_projected_second_order A B g hA hB hg hAsym Q hA0 hB0 hQ hpos k hk hpre
  have hproj : (fun z => Matrix.toEuclideanCLM (𝕜 := ℝ) (R z)ᵀ
      (probedGradient m (A z) (B z) (g z) (k+1))+c z) =O[𝓝 (0 : X)] (fun z => ‖z‖^3) := by
    simpa only [projectedResidual_fullBasisMatrix] using hnative
  have hf := full_projection_reconstruction_order R _ c hR hu hc hproj
  simpa only [R,c,map_mul,mul_apply_eq_comp] using hf

end
end krylov.Correction
