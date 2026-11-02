import krylov.Convergence.ObservableDomainSource
import krylov.Convergence.ObservableSpectralUniform

/-!
Article: main_krylov, apG:Dunif, explicit proper-domain uniform bounds.
Use: retain exactly the same universal radius and constant on genuine
open convex self-concordant domains containing the fixed canonical ball.
All actual cycle/inverse/energy/value hypotheses remain conclusions.
Source: the derived local-domain source and the original native FC/RFC
first-stopping theorems, with actual attained spectral condition data.
-/

/-!
Article: krylov, Proposition E.17 [apG:Dunif].

The literal observable restarting FC/RFC cycles satisfy the stated n^{3/2} quadratic/cubic
bounds on genuine self-concordant objectives, with an absolute constant and a radius depending
only on n,κ and the cutoff.
Undefined/non-descent stops, stationary points, failed energy gates, value acceptance and
proper domains containing the fixed canonical ball are all covered; no independence condition
is assumed.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric Matrix krylov.LinearAlgebra krylov.Functions krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}
/-- The same actual uniform bound on every admitted proper self-concordant domain.
Article: main_krylov, apG:Dunif. -/
theorem observable_fc_domain_uniform_selfConcordant
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (hn : 1≤n)
    (m ratio : ℝ) (hm : 0<m) (hr : 1≤ratio)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n),m^2*‖v‖^2 ≤ inner ℝ v (cgOperator base v))
    (hupper : ‖cgOperator base‖≤m^2*ratio^2)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (U : Set (EuclideanSpace ℝ (Fin n))) (D : StandardSelfConcordantData f U)
    (hgzero : gradient f 0=0) (hH : D.hessian 0=cgOperator base)
    (hdomain : ball (0:EuclideanSpace ℝ (Fin n)) (1/8)⊆(metricCoordinates base hb).symm ⁻¹' U)
    (bar : ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (hx₀ : ‖metricCoordinates base hb x₀‖≤observableFCRadius n ratio) :
    ‖metricCoordinates base hb (observableRestartPoint false bar (metricCoordinates base hb)
      f (gradient f) (1/64) n x₀)‖≤
      1024*(1+ratio)*(n:ℝ)*Real.sqrt n*‖metricCoordinates base hb x₀‖^2 := by
  obtain ⟨_hpos,hstart,hsmall,hsharp⟩ := observable_fc_radius_budgets hn ratio _ hr (norm_nonneg _) hx₀
  have hh := observable_fc_actual_cycle_bound base hb f (gradient f) D.hessian (1/64) 4
    (observable_selfConcordant_domain_source base hb f U D hgzero hH hdomain) m ratio hm hr hlower hupper
    bar x₀ hstart hsmall hsharp
  simpa only [NNReal.coe_ofNat,show (256:ℝ)*4=1024 by norm_num] using hh


/-- The same actual uniform bound on every admitted proper self-concordant domain.
Article: main_krylov, apG:Dunif. -/
theorem observable_rfc_domain_uniform_selfConcordant
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (hn : 1≤n)
    (m ratio : ℝ) (hm : 0<m) (hr : 1≤ratio)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n),m^2*‖v‖^2 ≤ inner ℝ v (cgOperator base v))
    (hupper : ‖cgOperator base‖≤m^2*ratio^2)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (U : Set (EuclideanSpace ℝ (Fin n))) (D : StandardSelfConcordantData f U)
    (hgzero : gradient f 0=0) (hH : D.hessian 0=cgOperator base)
    (hdomain : ball (0:EuclideanSpace ℝ (Fin n)) (1/8)⊆(metricCoordinates base hb).symm ⁻¹' U)
    (bar : ℝ) (hbar0 : 0<bar) (hbar : (n:ℝ)*bar≤1/16)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (hx₀ : ‖metricCoordinates base hb x₀‖≤observableRFCRadius n ratio bar) :
    ‖metricCoordinates base hb (observableRestartPoint true bar (metricCoordinates base hb)
      f (gradient f) (1/64) n x₀)‖≤
      134217728*(ratio^2/bar)*(n:ℝ)*Real.sqrt n*‖metricCoordinates base hb x₀‖^3 := by
  obtain ⟨_hpos,hstart,hsmall,hsharp,hshort⟩ := observable_rfc_radius_budgets hn ratio bar _
    hr hbar0 (norm_nonneg _) hx₀
  have hh := observable_rfc_actual_cycle_bound base hb hn f (gradient f) D.hessian (1/64) 4
    (observable_selfConcordant_domain_source base hb f U D hgzero hH hdomain) m ratio hm hr hlower hupper
    bar hbar0 hbar x₀ hstart hsmall hsharp hshort
  let a := (ratio^2/bar)*(n:ℝ)*Real.sqrt n*‖metricCoordinates base hb x₀‖^3
  have ha : 0≤a := by dsimp only [a];positivity
  calc
    _ ≤ 75497472*a := by
      convert hh using 1
      dsimp only [a,observableRFCResidualBudget]
      norm_num
      ring
    _ ≤ 134217728*a := mul_le_mul_of_nonneg_right (by norm_num) ha
    _ = _ := by dsimp only [a];ring


variable [NeZero n]

/-- The literal true-kappa FC estimate on a proper self-concordant domain,
with the original universal radius and C0. Article: apG:Dunif. -/
theorem observable_fc_true_kappa_domain_uniform
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (hn : 1≤n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (U : Set (EuclideanSpace ℝ (Fin n))) (D : StandardSelfConcordantData f U)
    (hgzero : gradient f 0=0) (hH : D.hessian 0=cgOperator base)
    (hdomain : ball (0:EuclideanSpace ℝ (Fin n)) (1/8)⊆(metricCoordinates base hb).symm ⁻¹' U)
    (bar : ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (hx₀ : ‖metricCoordinates base hb x₀‖≤1/(8192*(n:ℝ)*observableSpectralKappa base hb)) :
    ‖metricCoordinates base hb (observableRestartPoint false bar (metricCoordinates base hb)
      f (gradient f) (1/64) n x₀)‖≤
      observableUniformConstant*(1+Real.sqrt (observableSpectralKappa base hb))*(n:ℝ)*Real.sqrt n*
        ‖metricCoordinates base hb x₀‖^2 := by
  have hx : ‖metricCoordinates base hb x₀‖≤observableFCRadius n (Real.sqrt (observableSpectralKappa base hb)) := by
    rwa [observableFCRadius_exactKappa]
  have hd:=observable_spectral_data base hb
  have hh:=observable_fc_domain_uniform_selfConcordant base hb hn _ _ hd.1 hd.2.1 hd.2.2.1 hd.2.2.2
    f U D hgzero hH hdomain bar x₀ hx
  apply hh.trans
  dsimp only [observableUniformConstant,observableSpectralKappa]
  gcongr
  norm_num


/-- The literal true-kappa RFC estimate on a proper self-concordant domain,
with the same dimension/condition/cutoff radius and C0. Article: apG:Dunif. -/
theorem observable_rfc_true_kappa_domain_uniform
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (hn : 1≤n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (U : Set (EuclideanSpace ℝ (Fin n))) (D : StandardSelfConcordantData f U)
    (hgzero : gradient f 0=0) (hH : D.hessian 0=cgOperator base)
    (hdomain : ball (0:EuclideanSpace ℝ (Fin n)) (1/8)⊆(metricCoordinates base hb).symm ⁻¹' U)
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
  have hh:=observable_rfc_domain_uniform_selfConcordant base hb hn _ _ hd.1 hd.2.1 hd.2.2.1 hd.2.2.2
    f U D hgzero hH hdomain bar hbar0 hbar x₀ hx
  have hs : (Real.sqrt (spectralUpper base hb.1/spectralLower base hb.1))^2=
      spectralUpper base hb.1/spectralLower base hb.1:=Real.sq_sqrt (observableSpectralKappa_pos base hb).le
  simpa only [observableUniformConstant,observableSpectralKappa,hs] using hh


end
end krylov.Convergence
