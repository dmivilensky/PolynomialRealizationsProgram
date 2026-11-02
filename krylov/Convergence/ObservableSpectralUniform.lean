import krylov.Convergence.ObservableSpectralData
import krylov.Convergence.ObservableRFCSelfConcordant

/-!
Article: main_krylov, apG:Dunif, literal true-kappa observable bounds.
Use: state both actual FC/RFC cycle estimates with the true spectrum of
Hstar, explicit before-function radii, and one common absolute constant.
Source: genuine finite spectral extrema and the proved primitive-source
observable-cycle theorems. No compact reference/nonstagnation is assumed.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.LinearAlgebra krylov.Functions krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ} [NeZero n]

/-- The actual spectral condition number of the nonempty true Hessian. -/
def observableSpectralKappa (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) : ℝ :=
  spectralUpper base hb.1/spectralLower base hb.1

/-- One universal constant works for both printed observable methods. -/
def observableUniformConstant : ℝ:=134217728

/-- The true condition number is positive, by actual positive spectral
endpoint attainment. -/
theorem observableSpectralKappa_pos (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) :
    0<observableSpectralKappa base hb := div_pos (spectralUpper_pos base hb) (spectralLower_pos base hb)

/-- The admitted FC radius is literally inverse-linear in true kappa. -/
theorem observableFCRadius_exactKappa (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) :
    observableFCRadius n (Real.sqrt (observableSpectralKappa base hb))=
      1/(8192*(n:ℝ)*observableSpectralKappa base hb) := by
  simp only [observableFCRadius,Real.sq_sqrt (observableSpectralKappa_pos base hb).le]

/-- The admitted RFC radius is literally the printed condition/cutoff
minimum, and is fixed before any scalar function is selected. -/
theorem observableRFCRadius_exactKappa (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (bar : ℝ) :
    observableRFCRadius n (Real.sqrt (observableSpectralKappa base hb)) bar=
      min (1/(1048576*(n:ℝ)*observableSpectralKappa base hb)) (bar/(1024*(n:ℝ))) := by
  simp only [observableRFCRadius,Real.sq_sqrt (observableSpectralKappa_pos base hb).le]

/-- The complete actual observable FC result with literal true kappa,
explicit uniform radius and the common absolute constant C0. -/
theorem observable_fc_true_kappa_uniform
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (hn : 1≤n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (D : StandardSelfConcordantData f Set.univ)
    (hgzero : gradient f 0=0) (hH : D.hessian 0=cgOperator base)
    (bar : ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (hx₀ : ‖metricCoordinates base hb x₀‖≤1/(8192*(n:ℝ)*observableSpectralKappa base hb)) :
    ‖metricCoordinates base hb (observableRestartPoint false bar (metricCoordinates base hb)
      f (gradient f) (1/64) n x₀)‖≤
      observableUniformConstant*(1+Real.sqrt (observableSpectralKappa base hb))*(n:ℝ)*Real.sqrt n*
        ‖metricCoordinates base hb x₀‖^2 := by
  have hx : ‖metricCoordinates base hb x₀‖≤observableFCRadius n (Real.sqrt (observableSpectralKappa base hb)) := by
    rwa [observableFCRadius_exactKappa]
  have hh:=observable_fc_uniform_selfConcordant_kappa base hb hn f D hgzero hH bar x₀ hx
  apply hh.trans
  dsimp only [observableUniformConstant,observableSpectralKappa]
  gcongr
  norm_num

/-- The complete actual observable RFC result with literal true kappa,
explicit before-function radius and the same absolute constant C0.
Every real inverse/descent/energy/value decision belongs to the executor. -/
theorem observable_rfc_true_kappa_uniform
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (hn : 1≤n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (D : StandardSelfConcordantData f Set.univ)
    (hgzero : gradient f 0=0) (hH : D.hessian 0=cgOperator base)
    (bar : ℝ) (hbar0 : 0<bar) (hbar : (n:ℝ)*bar≤1/16)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (hx₀ : ‖metricCoordinates base hb x₀‖≤
      min (1/(1048576*(n:ℝ)*observableSpectralKappa base hb)) (bar/(1024*(n:ℝ)))) :
    ‖metricCoordinates base hb (observableRestartPoint true bar (metricCoordinates base hb)
      f (gradient f) (1/64) n x₀)‖≤
      observableUniformConstant*(observableSpectralKappa base hb/bar)*(n:ℝ)*Real.sqrt n*
        ‖metricCoordinates base hb x₀‖^3 := by
  have hd:=observable_spectral_data base hb
  have hx : ‖metricCoordinates base hb x₀‖≤observableRFCRadius n (Real.sqrt (observableSpectralKappa base hb)) bar := by
    rwa [observableRFCRadius_exactKappa]
  have hh:=observable_rfc_uniform_selfConcordant base hb hn _ _ hd.1 hd.2.1 hd.2.2.1 hd.2.2.2
    f D hgzero hH bar hbar0 hbar x₀ hx
  have hs : (Real.sqrt (spectralUpper base hb.1/spectralLower base hb.1))^2=
      spectralUpper base hb.1/spectralLower base hb.1:=Real.sq_sqrt (observableSpectralKappa_pos base hb).le
  simpa only [observableUniformConstant,observableSpectralKappa,hs] using hh

end
end krylov.Convergence
