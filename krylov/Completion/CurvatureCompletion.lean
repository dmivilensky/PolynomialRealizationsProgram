import krylov.Completion.SpectralExtension
import krylov.Completion.ScalarSchur
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau, exact physical curvature completions.
Use: combine the singular Schur interval with a constructed physical spectral
extension; both endpoint curvatures are genuinely realizable matrices.
Source: Albert69 and the proved finite orthogonal-column extension.
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.LinearAlgebra
variable {n p : ℕ}

/-- The exact feasible curvature interval for a physical full-rank augmented
frame, retaining singular shifted blocks and both genuine range conditions.
Use: endpoint values are attained by actual physical matrices, not postulated
as an abstract completion interval.
Article: main_krylov, thm:radau.
Proof: use the proved physical extension equivalence and then both scalar
generalized Schur tests. Neither shifted old block is inverted. -/
theorem curvature_completion_iff
    (Z : Matrix (Fin n) (Fin 1 ⊕ Fin p) ℝ) (hZ : (Zᵀ*Z).PosDef)
    (G T : Matrix (Fin p) (Fin p) ℝ) (b : Matrix (Fin p) (Fin 1) ℝ)
    (D mu L c : ℝ) (hmuL : mu≤L)
    (hGram : Zᵀ*Z=windowAugmentedGram G b D)
    (hlo : (T-mu • G).PosSemidef) (hhi : (L • G-T).PosSemidef) :
    (∃ A : Matrix (Fin n) (Fin n) ℝ,
      (A-mu • 1).PosSemidef ∧ (L • 1-A).PosSemidef ∧
        Zᵀ*A*Z=windowCurvatureForm T c) ↔
      (LinearMap.range ((-mu) • b).mulVecLin≤LinearMap.range (T-mu • G).mulVecLin) ∧
      (LinearMap.range (L • b).mulVecLin≤LinearMap.range (L • G-T).mulVecLin) ∧
      mu*D+mu^2*(bᵀ*pseudoinverse (T-mu • G) hlo.1*b) 0 0≤c ∧
        c≤L*D-L^2*(bᵀ*pseudoinverse (L • G-T) hhi.1*b) 0 0 := by
  rw [← spectral_extension_iff Z hZ (windowCurvatureForm T c) mu L hmuL,hGram,
    lower_curvature_test G T b D c mu hlo,upper_curvature_test G T b D c L hhi]
  tauto

/-- Every curvature between the singular Schur endpoints has an actual
physical completion in the closed spectral band.
Use: construct both endpoint scenarios by substituting the interval endpoints.
Article: main_krylov, thm:radau.
Proof: all feasibility assumptions concern known compressed data; the exact
completion equivalence constructs the physical matrix at the chosen curvature. -/
theorem curvature_completion_exists
    (Z : Matrix (Fin n) (Fin 1 ⊕ Fin p) ℝ) (hZ : (Zᵀ*Z).PosDef)
    (G T : Matrix (Fin p) (Fin p) ℝ) (b : Matrix (Fin p) (Fin 1) ℝ)
    (D mu L c : ℝ) (hmuL : mu≤L)
    (hGram : Zᵀ*Z=windowAugmentedGram G b D)
    (hlo : (T-mu • G).PosSemidef) (hhi : (L • G-T).PosSemidef)
    (hrlo : LinearMap.range ((-mu) • b).mulVecLin≤LinearMap.range (T-mu • G).mulVecLin)
    (hrhi : LinearMap.range (L • b).mulVecLin≤LinearMap.range (L • G-T).mulVecLin)
    (hclo : mu*D+mu^2*(bᵀ*pseudoinverse (T-mu • G) hlo.1*b) 0 0≤c)
    (hchi : c≤L*D-L^2*(bᵀ*pseudoinverse (L • G-T) hhi.1*b) 0 0) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ,
      (A-mu • 1).PosSemidef ∧ (L • 1-A).PosSemidef ∧ Zᵀ*A*Z=windowCurvatureForm T c :=
  (curvature_completion_iff Z hZ G T b D mu L c hmuL hGram hlo hhi).mpr ⟨hrlo,hrhi,hclo,hchi⟩

end
end krylov.Completion
