import krylov.Methods.DirectBroydenPhysical
import krylov.LinearAlgebra.MatrixLimits
import krylov.Methods.SecantSolve
import krylov.Secant.CorrectionOrder
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(c), complete native final inverse comparison.
Use: the genuine full-memory direct quasi-Newton inverse step agrees with
the latest-information correction on its own pairs up to O(t² times norm g).
Source: proved native model comparison, actual independent reference steps,
positive reference Gram form and the genuine full-basis resolvent calculus.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference krylov.Stability krylov.LinearAlgebra krylov.Secant
open Matrix Filter Topology Asymptotics
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {α : Type*} {n : ℕ} {l : Filter α} {t : α → ℝ}

/-- The literal full native direct quasi-Newton inverse model and the
actual latest-information inverse action on its own observed pairs differ
by second order in the original physical spectral norm.
Use: closes the full-memory inverse-matrix conclusion of the source.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: actual observed pair limits give the positive reference Gram limit.
True independent reference steps give the genuine nonsingular basis limit.
The proved native quadratic compression identity and actual resolvent
calculus derive every inverse domain and the actual full inverse estimate. -/
theorem directBroyden_physical_inverse_second_order
    (D : DirectBroydenPerturbation (E := EuclideanSpace ℝ (Fin n)) l t n)
    (hli : LinearIndependent ℝ (fun i : Fin n => D.referenceStep i.val)) :
    (fun z => (directBroydenPhysicalModel D z)⁻¹-
      directBroydenPhysicalSteps D z*(latest (directBroydenPhysicalObserved D z))⁻¹*
        (directBroydenPhysicalSteps D z)ᵀ) =O[l] (fun z => t z^2) := by
  let S0 : Matrix (Fin n) (Fin n) ℝ := fun i j => D.referenceStep j.val i
  let T0 := crossGram (fun i : Fin n => D.reference (D.referenceStep i.val))
    (fun i => D.referenceStep i.val)
  have hTpos : T0.PosDef := operatorGram_posDef D.reference D.reference_symmetric D.reference_positive hli
  have hT0 : IsUnit T0.det := isUnit_iff_ne_zero.mpr hTpos.det_pos.ne'
  have hcol : LinearIndependent ℝ S0.col :=
    hli.map' (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).injective)
  have hS0 : IsUnit S0.det := (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_cols_iff_isUnit.mp hcol)
  have hS : Tendsto (directBroydenPhysicalSteps D) l (𝓝 S0) := by
    apply matrix_tendsto_of_entries
    intro i j
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).continuous.continuousAt.tendsto).comp (D.step_limit j.val j.isLt)
  have hT : Tendsto (fun z => latest (directBroydenPhysicalObserved D z)) l (𝓝 T0) := by
    apply matrix_tendsto_of_entries
    intro i j
    have hh := (D.step_limit (min i j).val (min i j).isLt).inner (𝕜 := ℝ)
      (directBroydenPerturbation_limits D (max i j).val (max i j).isLt).1
    have hs : T0.IsSymm := Matrix.isHermitian_iff_isSymm.mp hTpos.1
    have he : inner ℝ (D.referenceStep (min i j).val)
        (D.reference (D.referenceStep (max i j).val))=T0 i j := by
      have he0 : inner ℝ (D.referenceStep (min i j).val)
          (D.reference (D.referenceStep (max i j).val))=T0 (min i j) (max i j) :=
        (D.reference_symmetric _ _).symm
      exact he0.trans (congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) (latest_eq_of_isSymm hs))
    rw [← he]
    exact hh
  exact full_basis_inverse_order (directBroydenPhysicalSteps D) (directBroydenPhysicalModel D)
    (fun z => latest (directBroydenPhysicalObserved D z)) S0 T0 hS0 hT0 (fun z => t z^2)
    (by simpa only [zero_pow (by decide : 2≠0)] using D.scale_limit.pow 2) hS hT
    (directBroyden_physical_model_second_order D)

/-- The actual full native quasi-Newton inverse step agrees with the
latest-information correction on its own genuine pairs up to O(t² norm g),
for an arbitrary actual final gradient, with no bounded-gradient premise.
Use: the source final-step comparison retains the true returned gradient.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: transfer the proved genuine spectral inverse difference through
the isometric physical operator dictionary and apply its actual operator
norm bound to the arbitrary genuine gradient. -/
theorem directBroyden_physical_final_step_second_order
    (D : DirectBroydenPerturbation (E := EuclideanSpace ℝ (Fin n)) l t n)
    (hli : LinearIndependent ℝ (fun i : Fin n => D.referenceStep i.val))
    (g : α → EuclideanSpace ℝ (Fin n)) :
    (fun z => -(Matrix.toEuclideanCLM (𝕜 := ℝ) ((directBroydenPhysicalModel D z)⁻¹) (g z))+
      Matrix.toEuclideanCLM (𝕜 := ℝ) (directBroydenPhysicalSteps D z*
        (latest (directBroydenPhysicalObserved D z))⁻¹*(directBroydenPhysicalSteps D z)ᵀ) (g z))
      =O[l] (fun z => t z^2*‖g z‖) := by
  have h := matrix_bigO_toEuclideanCLM _ _ (directBroyden_physical_inverse_second_order D hli)
  have hg : g =O[l] (fun z => ‖g z‖) := (isBigO_refl g l).norm_right
  have he := clm_apply_bigO _ g _ _ h hg
  exact he.neg_left.congr_left (fun z => by
    simp only [map_sub,_root_.sub_apply]
    abel)

end
end krylov.Methods
