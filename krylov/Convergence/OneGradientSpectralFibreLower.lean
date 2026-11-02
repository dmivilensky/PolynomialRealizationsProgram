import krylov.Convergence.OneGradientFixedFibreDelta
import krylov.OneGradient.SpectralSharpSupremum
set_option maxHeartbeats 800000

/-!
Article: main_krylov, thm:LB, original spectral information fibre.
Use: specialize the genuine scalar lower bound to the actual measured
Gauss--Radau Schur endpoints. All positivity, information, hidden-axis,
last-length, spectrum and minimax premises are derived from the original
full-atom reference in the given spectral class.
Source: actual physical Lanczos information fibres and their proved closed
spectral endpoint and reciprocal-CG-length dictionaries.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set chebyshev1 krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ} {μ L : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin (n+2))

/-- The original true two-sided matrix spectral prior gives the actual
labelled spectral bounds and real lower quadratic form. Article: thm:LB. -/
theorem oneGradient_actual_spectral_band
    {d : ℕ} (C : Matrix (Fin d) (Fin d) ℝ) (hC : C.PosDef) (μ L : ℝ)
    (hlo : (C-μ • 1).PosSemidef) (hhi : (L • 1-C).PosSemidef) :
    (∀ i,μ≤hC.1.eigenvalues i ∧hC.1.eigenvalues i≤L) ∧
      ∀ v : EuclideanSpace ℝ (Fin d),μ*‖v‖^2≤ inner ℝ v (cgOperator C v) := by
  let B := SpectralBasis.ofHermitian C hC.1
  have hl : ((-μ) • (1 : Matrix (Fin d) (Fin d) ℝ)+C).PosSemidef := by
    convert hlo using 1; module
  have hl' := (coordinates_posSemidef_iff B _).mpr hl
  have hh' := (coordinates_posSemidef_iff B _).mpr hhi
  rw [coordinates_lower_shift,posSemidef_diagonal_iff] at hl'
  rw [coordinates_upper_shift,posSemidef_diagonal_iff] at hh'
  have hband : ∀ i,μ≤hC.1.eigenvalues i ∧hC.1.eigenvalues i≤L := by
    intro i
    change μ≤B.eigenvalues i ∧B.eigenvalues i≤L
    exact ⟨by linarith only [hl' i],sub_nonneg.mp (hh' i)⟩
  exact ⟨hband,spectral_lower_form C hC.1 (fun i=>(hband i).1)⟩

/-- Fixed realizable normalized information forces the original printed
rho(I) lower bound on genuine scalar cubic functions. This theorem uses
only an actual full-atom reference in the original spectral class; every
endpoint and hidden-normal hypothesis is derived. The true Hessian can
lie within delta*mu of the actual endpoint selected by the method.
Article: main_krylov, thm:LB, fixed-information assertion. -/
theorem oneGradient_spectral_fibre_true_lower
    (P : SpectralPriorReference n μ L) (hμ : 0<μ) (hμL : μ≤L)
    (Mhat δ : ℝ) (hMhat : 0<Mhat) (hδ : 0<δ) (hδ1 : δ<1) :
    let lo:=spectralLowerPivot P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support μ
    let hi:=spectralUpperPivot P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support L
    let a:=lastLanczosVector P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support
    ∃ s : ℝ,0<s ∧∀ h : ℝ,0<h → h<s →∀ method : OneGradientMethod E,
      OneGradientSpanRestricted method →
      ∃ b∈({lo,hi} : Set ℝ), ∃ R : ℝ,0<R ∧
        ∃ w : OneGradientCubicLowerWitness method
          (lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b)
          (h • P.gradient) a R ((1+δ)*Mhat) ((1-δ)*(Mhat/2)*spectralPriorCoefficient P),
          ‖oneGradientCubicTrueHessian
            (lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b)
            a w.curvature w.cubic w.minimizer-
            lanczosCompletion P.matrix P.positive P.gradient P.gradient_ne_zero P.full_support b‖≤δ*μ ∧
          ∀ i,μ*(1-δ)≤w.positive.1.eigenvalues i ∧w.positive.1.eigenvalues i≤L*(1+δ) := by
  let A:=P.matrix
  let g:=P.gradient
  let lo:=spectralLowerPivot A P.positive g P.gradient_ne_zero P.full_support μ
  let hi:=spectralUpperPivot A P.positive g P.gradient_ne_zero P.full_support L
  let C₀:=lanczosCompletion A P.positive g P.gradient_ne_zero P.full_support hi
  let C₁:=lanczosCompletion A P.positive g P.gradient_ne_zero P.full_support lo
  let a:=lastLanczosVector A P.positive g P.gradient_ne_zero P.full_support
  let σ:=lastJacobiPivot A P.positive g P.gradient_ne_zero P.full_support-
    (lastInversePivot A P.positive g P.gradient_ne_zero P.full_support)⁻¹
  obtain ⟨horder,hlo,hhi⟩ := spectral_fibre_endpoint_band A P.positive g P.gradient_ne_zero P.full_support μ L
    (spectral_prior_nonempty_fibre P)
  have hC₀ : C₀.PosDef := spectral_fibre_completion_positive A P.positive g P.gradient_ne_zero P.full_support μ hi hμ hhi.1
  have hC₁ : C₁.PosDef := spectral_fibre_completion_positive A P.positive g P.gradient_ne_zero P.full_support μ lo hμ hlo.1
  obtain ⟨hband₀,hbase₀⟩ := oneGradient_actual_spectral_band C₀ hC₀ μ L hhi.1 hhi.2
  obtain ⟨hband₁,hbase₁⟩ := oneGradient_actual_spectral_band C₁ hC₁ μ L hlo.1 hlo.2
  have hlength₀ : CG.length (cgOperator C₀) g (n+1)=1/(hi-σ) := by
    rw [completion_last_cg_length]
    congr 1
    dsimp only [σ]
    ring
  have hlength₁ : CG.length (cgOperator C₁) g (n+1)=1/(lo-σ) := by
    rw [completion_last_cg_length]
    congr 1
    dsimp only [σ]
    ring
  have hgap : 0<lo-σ := hμ.trans (spectral_fibre_endpoint_gaps A P.positive g P.gradient_ne_zero P.full_support μ L hμ
    (spectral_prior_nonempty_fibre P)).1
  have hlenorder : CG.length (cgOperator C₀) g (n+1)≤CG.length (cgOperator C₁) g (n+1) := by
    rw [hlength₀,hlength₁]
    exact one_div_le_one_div_of_le hgap (sub_le_sub_right horder σ)
  have hρ : intervalMinimaxValue (CG.length (cgOperator C₀) g (n+1)) (CG.length (cgOperator C₁) g (n+1))=
      spectralPriorCoefficient P := by
    rw [hlength₀,hlength₁]
    rfl
  obtain ⟨s,hs,hsource⟩ := oneGradient_fixed_fibre_delta_true_lower A C₀ C₁ P.positive hC₀ hC₁ g a
    (last_lanczos_unit A P.positive g P.gradient_ne_zero P.full_support)
    (full_gradient_atom_count A P.positive g P.full_support)
    (lanczos_completion_information A P.positive g P.gradient_ne_zero P.full_support hi)
    (lanczos_completion_information A P.positive g P.gradient_ne_zero P.full_support lo)
    (krylov_last_lanczos_hyperplane A P.positive g P.gradient_ne_zero P.full_support)
    hlenorder Mhat μ L δ hMhat hμ hμL hδ hδ1 hbase₀ hbase₁ hband₀ hband₁
  rw [hρ] at hsource
  refine ⟨s,hs,?_⟩
  intro h hh hhsmall method hmeth
  obtain ⟨C,hCmem,R,hR,w,hw⟩ := hsource h hh hhsmall method hmeth
  rcases hCmem with hCeq|hCeq
  · subst C
    exact ⟨hi,Or.inr rfl,R,hR,w,hw⟩
  · rw [mem_singleton_iff] at hCeq
    subst C
    exact ⟨lo,Or.inl rfl,R,hR,w,hw⟩

end
end krylov.Convergence
