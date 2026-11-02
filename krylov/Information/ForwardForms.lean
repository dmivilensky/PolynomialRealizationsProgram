import krylov.Information.FormCoordinates
import krylov.Information.PlanarAdmissibility

/-!
Article: main_krylov, s4:cor-Q and thm:centre, original forward physical form transport.
Use: original physical source positivity and every primitive admissibility
budget survive the genuine common direction-coordinate congruence exactly.
Source: actual congruence positivity, proved relative-budget invariance and
the existing complete inverse-form physical admissibility transport.
-/

namespace krylov.Information
noncomputable section
open Matrix krylov.Reference krylov.Methods krylov.Secant
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A genuine full direction-coordinate congruence preserves positive definiteness of the actual physical base.
Use: derive the original common-coordinate metric domain from real direction rank.
Article: main_krylov, s4:cor-Q and thm:centre, genuine forward coordinate admissibility.
Proof: the actual direction matrix is injective by its genuine inverse, so the proved positive-form congruence theorem applies. -/
theorem formMap_posDef (D A : Matrix (Fin n) (Fin n) ℝ) (hD : IsUnit D.det) (hA : A.PosDef) :
    (formMap D A).PosDef := by
  have hi : Function.Injective D.mulVec := by
    intro u v huv
    have hh := congrArg (fun x => D⁻¹*ᵥx) huv
    simpa only [mulVec_mulVec,nonsing_inv_mul _ hD,one_mulVec] using hh
  change (Dᵀ*A*D).PosDef
  simpa only [conjTranspose_eq_transpose_of_trivial] using hA.conjTranspose_mul_mul_same (B := D) hi

/-- Actual forward direction-coordinate congruence preserves symmetry of every original physical source form.
Use: the physical source primitive symmetry conditions apply directly to the real coordinate reflection.
Article: main_krylov, s4:cor-Q and thm:centre, genuine forward coordinate admissibility.
Proof: transposing the original real congruence returns the same actual symmetric form. -/
theorem formMap_isSymm (D A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) :
    (formMap D A).IsSymm := by
  change (Dᵀ*A*D)ᵀ=Dᵀ*A*D
  simp only [transpose_mul,transpose_transpose,hA.eq,Matrix.mul_assoc]

/-- The genuine forward direction-coordinate congruence preserves every original symmetric relative spectral budget exactly.
Use: retain the source's individual budget profile and quantitative slack without an extra normalization loss.
Article: main_krylov, s4:cor-Q and thm:centre, genuine forward coordinate admissibility.
Proof: apply the existing exact relative-budget congruence theorem on the actual full direction domain. -/
theorem formMap_budget (D A E : Matrix (Fin n) (Fin n) ℝ) (hD : IsUnit D.det)
    (hA : A.PosDef) (hE : E.IsSymm) :
    relativeBudget (formMap D A) (formMap D E)=relativeBudget A E := relativeBudget_congruence A E D hA hE hD

/-- Inverse physical transport through the actual inverse direction matrix equals the original forward coordinate congruence.
Use: reuse the existing full physical-source admissibility theorem for the genuine forward coordinate map.
Article: main_krylov, s4:cor-Q and thm:centre, genuine forward coordinate admissibility.
Proof: the actual inverse transpose and inverse are nonsingular and cancel back to the two original direction factors. -/
theorem inverseFormMap_inverse (D : Matrix (Fin n) (Fin n) ℝ) (hD : IsUnit D.det) :
    inverseFormMap D⁻¹=formMap D := by
  ext X i j
  change ((D⁻¹)ᵀ⁻¹*X*(D⁻¹)⁻¹) i j=(Dᵀ*X*D) i j
  rw [transpose_nonsing_inv,nonsing_inv_nonsing_inv _ hD,
    nonsing_inv_nonsing_inv _ (by simpa only [det_transpose] using hD)]

/-- Every genuinely admissible original physical source scenario is admissible with the identical primitive budget profile in its true full direction coordinates.
Use: the source reference ball, increments and independent corrections keep their exact original constraints before reflecting.
Article: main_krylov, s4:cor-Q and thm:centre, genuine forward coordinate admissibility.
Proof: identify the genuine forward coordinate map with inverse transport through the true inverse direction matrix and reuse the proved complete physical admissibility theorem. -/
theorem Scenario.inCoordinates_admissible (S : Scenario n) (N : ℕ)
    (A D : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) (hD : IsUnit D.det)
    (r : ℝ) (ω : ℕ → ℝ) (w τ : ℝ) (hS : S.Admissible N A r ω w τ) :
    (S.inCoordinates D).Admissible N (formMap D A) r ω w τ := by
  have ht := S.inPhysical_admissible N A D⁻¹ hA (Matrix.isUnit_nonsing_inv_det _ hD) r ω w τ hS
  simpa only [Scenario.inPhysical,Scenario.inCoordinates,inverseFormMap_inverse D hD] using ht

end
end krylov.Information
