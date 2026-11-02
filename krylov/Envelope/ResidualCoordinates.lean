import krylov.Envelope.TiltSplitting

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu, genuine observed residual coordinate reconstruction.
Use: identify actual residual-variation vectors from their true executed
step/gradient residual derivatives in the genuine finite CG prefix frame.
Source: proved actual explored orthogonal projection formula and genuine
positive nonstagnating CG step normalizers.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix Finset
open scoped BigOperators
variable {n : ℕ}

/-- A genuine explored vector whose true canonical step coordinates equal the actual recorded residual derivatives is exactly the real residual-variation vector.
Use: A genuine explored vector whose true canonical step coordinates equal the actual recorded residual derivatives is exactly the real residual-variation vector.
Article: main_krylov, apB:lem:mu, genuine observed residual coordinate reconstruction.
Proof: Project the actual vector in the genuine orthonormal CG prefix and cancel only the proved true nonzero recorded-step normalizers. -/
theorem residualVariation_of_coordinates (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : N≤referenceAtomCount base hb g)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (A B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (F : EuclideanSpace ℝ (Fin n)) (hF : F∈exploredFlag base g N)
    (hcoordinates : ∀ i<N, deriv (fun t => inner ℝ (probedStep m (A t) (B t) g i)
      (probedGradient m (A t) (B t) g N)) 0=inner ℝ (canonicalCGStep base g i) F) :
    residualVariation base g m A B N=F := by
  -- Reconstruct the genuine vector by its actual explored CG projection before dividing the real residual coordinates by true nonzero step norms.
  have hfix : (exploredFlag base g N).starProjection F=F := (exploredFlag base g N).starProjection_eq_self_iff.mpr hF
  rw [← hfix,exploredFlag_projection base hb g hN,residualVariation]
  apply sum_congr rfl
  intro i _
  have hr : ‖canonicalCGStep base g i.val‖≠0 := norm_ne_zero_iff.mpr
    (canonicalCGStep_ne_zero base hb g i.val (fun j hj => cg_nonstagnation base hb g j (by have := i.isLt;omega)))
  have hunit : canonicalCGStep base g i.val=‖canonicalCGStep base g i.val‖ • canonicalCGUnitStep base g i.val :=
    (NormedSpace.norm_smul_normalize _).symm
  have hh := hcoordinates i.val i.isLt
  rw [hunit,real_inner_smul_left] at hh
  rw [hh]
  congr 1
  exact mul_div_cancel_left₀ _ hr
end
end krylov.Envelope
