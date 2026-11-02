import krylov.Methods.CanonicalWindows
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
Article: main_krylov, lem:U(a), the genuine continuous initial-error weight.
Use: discharge continuity and positivity of the actual inverse-root energy
norm on compact positive quadratic references; no unspecified weight remains.
Source: mathlib's continuous functional calculus square-root continuity on
the positive cone and actual matrix inverse continuity at a nonzero determinant.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Secant krylov.Methods
open scoped MatrixOrder Matrix.Norms.L2Operator Topology
variable {X : Type*} [TopologicalSpace X] {n : ℕ}

/-- The actual canonical root acts as a continuously varying Euclidean operator on positive continuous reference families.
Use: compact canonical budget conversion needs only the true root's continuity and its actual compact norm bound.
Article: main_krylov, prop:conv and lem:U.
Proof: continuous functional calculus gives the real positive square root;
the matrix-to-Euclidean-operator identification is an isometry in the genuine
spectral norm, so its composition is continuous. -/
theorem canonical_root_continuousOn (base : X → Matrix (Fin n) (Fin n) ℝ) (K : Set X)
    (hb : ContinuousOn base K) (hpos : ∀ x∈K, (base x).PosDef) :
    ContinuousOn (fun x => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base x))) K := by
  have hroot : ContinuousOn (fun x => metricRoot (base x)) K :=
    CFC.continuousOn_sqrt.comp hb (fun x hx => (hpos x hx).posSemidef.nonneg)
  exact (AddMonoidHomClass.isometry_of_norm (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ))
    (fun _ => rfl)).continuous.comp_continuousOn hroot

/-- The genuine canonical initial-error norm is continuous on any continuous family of positive quadratic references.
Use: supplies the actual weight ‖e₀‖_A in the compact FC/RFC Taylor theorem.
Article: main_krylov, lem:U(a).
Proof: the actual positive square root is continuous on the positive cone;
its proved nonzero determinant gives continuity of its actual inverse, and
continuous finite matrix-vector evaluation and the norm complete the claim. -/
theorem canonical_error_continuousOn (base : X → Matrix (Fin n) (Fin n) ℝ)
    (g : X → EuclideanSpace ℝ (Fin n)) (K : Set X)
    (hb : ContinuousOn base K) (hg : ContinuousOn g K) (hpos : ∀ x∈K, (base x).PosDef) :
    ContinuousOn (fun x => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base x))⁻¹ (g x)‖) K := by
  -- The square root and inverse are the actual source metric, not auxiliary whitening witnesses.
  have hroot : ContinuousOn (fun x => metricRoot (base x)) K :=
    CFC.continuousOn_sqrt.comp hb (fun x hx => (hpos x hx).posSemidef.nonneg)
  intro x hx
  have hi : ContinuousAt (fun M : Matrix (Fin n) (Fin n) ℝ => M⁻¹) (metricRoot (base x)) := by
    apply continuousAt_matrix_inv
    rw [show (Ring.inverse : ℝ → ℝ)=Inv.inv from funext Ring.inverse_eq_inv]
    exact continuousAt_inv₀ (isUnit_iff_ne_zero.mp (metricRoot_det_unit _ (hpos x hx)))
  have hinv : ContinuousWithinAt (fun z => (metricRoot (base z))⁻¹) K x :=
    hi.comp_continuousWithinAt (f := fun z : X => metricRoot (base z)) (hroot x hx)
  exact (Matrix.continuous_uncurry_toEuclideanCLM.continuousAt.comp_continuousWithinAt
    (hinv.prodMk (hg x hx))).norm

/-- A nonzero actual initial gradient has strictly positive genuine canonical initial-error norm.
Use: the source's error factor has a positive compact minimum on nondegenerate references.
Article: main_krylov, lem:U(a).
Proof: the actual inverse root has the actual root as a left inverse, so it cannot kill a nonzero gradient. -/
theorem canonical_error_pos (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) :
    0<‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g‖ := by
  -- Apply the genuine root to a hypothetical zero inverse-root image and cancel the actual inverse.
  apply norm_pos_iff.mpr
  intro hz
  have he := congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)) hz
  simp only [map_zero] at he
  have hi : (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g)=g := by
    rw [← mul_apply_eq_comp,← map_mul,
      Matrix.mul_nonsing_inv _ (metricRoot_det_unit base hb),map_one,one_apply_eq_self]
  exact hg (hi.symm.trans he)

end
end krylov.Stability
