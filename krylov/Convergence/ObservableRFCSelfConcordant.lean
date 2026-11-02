import krylov.Convergence.ObservableRFCCycle
import krylov.Convergence.ObservableSelfConcordant

/-!
Article: main_krylov, apG:Dunif, uniform observed RFC on true functions.
Use: fix the radius before the scalar source and conclude the printed
dimension/condition/cutoff dependence for the actual first-stopping cycle.
Source: true standard self-concordance supplies all local derivatives;
the complete native RFC theorem supplies every stopping alternative.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Functions krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace NNReal
variable {n : ℕ}

/-- Explicit positive radius depending only on dimension, the true
condition bound and the chosen observable cutoff. Article: apG:Dunif. -/
def observableRFCRadius (n : ℕ) (ratio bar : ℝ) : ℝ :=
  min (1/(1048576*(n:ℝ)*ratio^2)) (bar/(1024*(n:ℝ)))

/-- The same dimension/condition/cutoff radius supplies every analytic
allowance before the actual function is chosen. Article: apG:Dunif. -/
theorem observable_rfc_radius_budgets (hn : 1≤n) (ratio bar e : ℝ)
    (hr : 1≤ratio) (hb : 0<bar) (he : 0≤e) (hsize : e≤observableRFCRadius n ratio bar) :
    0<observableRFCRadius n ratio bar ∧ e<(1/64:ℝ)/4 ∧
      (n:ℝ)*(3*(4:ℝ)*e)≤1/128 ∧
      Real.sqrt n*(12*(4:ℝ)*e)≤Real.sqrt 3/(8*ratio^2) ∧
      12*Real.sqrt n*(3*(4:ℝ)*e)≤bar/4 := by
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hr2 : 1≤ratio^2 := by nlinarith only [hr,sq_nonneg (ratio-1)]
  have hfirst : e≤1/(1048576*(n:ℝ)*ratio^2) := hsize.trans (min_le_left _ _)
  have hsecond : e≤bar/(1024*(n:ℝ)) := hsize.trans (min_le_right _ _)
  have hden : 0<1048576*(n:ℝ)*ratio^2 := by positivity
  have hbig : e*(1048576*(n:ℝ)*ratio^2)≤1 := (le_div_iff₀ hden).mp hfirst
  have hne : e*(1024*(n:ℝ))≤bar := (le_div_iff₀ (by positivity : 0<1024*(n:ℝ))).mp hsecond
  have hnr : 1≤(n:ℝ)*ratio^2 := by nlinarith only [hn',hr2,mul_nonneg (sub_nonneg.mpr hn') (sub_nonneg.mpr hr2)]
  have he0 : e≤1/1048576 := by nlinarith only [hbig,mul_le_mul_of_nonneg_right hnr he]
  have hne0 : (n:ℝ)*e≤1/1048576 := by
    nlinarith only [hbig,mul_le_mul_of_nonneg_right hr2 (show 0≤(n:ℝ)*e by positivity)]
  have hsqrt : Real.sqrt n≤n := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith only [hn']⟩
  refine ⟨by dsimp only [observableRFCRadius];apply lt_min <;> positivity,
    by norm_num at he0 ⊢;linarith,by nlinarith only [hne0],?_,?_⟩
  · apply (le_div_iff₀ (by positivity : 0<8*ratio^2)).mpr
    have hh := mul_le_mul_of_nonneg_right hsqrt (show 0≤12*(4:ℝ)*e by positivity)
    have hh' := mul_le_mul_of_nonneg_right hh (show 0≤8*ratio^2 by positivity)
    have hbound : (Real.sqrt n*(12*(4:ℝ)*e))*(8*ratio^2)≤1/64 := by
      nlinarith only [hh',hbig]
    exact hbound.trans (Real.le_sqrt_of_sq_le (by norm_num))
  · have hh := mul_le_mul_of_nonneg_right hsqrt (show 0≤12*(3*(4:ℝ)*e) by positivity)
    nlinarith only [hh,hne,hb]

/-- The literal observable RFC cycle on every genuine standard
self-concordant function has an absolute cubic constant and the original
n^(3/2) kappa/bar dependence. All inverse, descent, energy and value
decisions are the actual ones. Article: main_krylov, apG:Dunif, RFC. -/
theorem observable_rfc_uniform_selfConcordant
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (hn : 1≤n)
    (m ratio : ℝ) (hm : 0<m) (hr : 1≤ratio)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n),m^2*‖v‖^2 ≤ inner ℝ v (cgOperator base v))
    (hupper : ‖cgOperator base‖≤m^2*ratio^2)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (D : StandardSelfConcordantData f Set.univ)
    (hgzero : gradient f 0=0) (hH : D.hessian 0=cgOperator base)
    (bar : ℝ) (hbar0 : 0<bar) (hbar : (n:ℝ)*bar≤1/16)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (hx₀ : ‖metricCoordinates base hb x₀‖≤observableRFCRadius n ratio bar) :
    ‖metricCoordinates base hb (observableRestartPoint true bar (metricCoordinates base hb)
      f (gradient f) (1/64) n x₀)‖≤
      134217728*(ratio^2/bar)*(n:ℝ)*Real.sqrt n*‖metricCoordinates base hb x₀‖^3 := by
  obtain ⟨_hpos,hstart,hsmall,hsharp,hshort⟩ := observable_rfc_radius_budgets hn ratio bar _
    hr hbar0 (norm_nonneg _) hx₀
  have hh := observable_rfc_actual_cycle_bound base hb hn f (gradient f) D.hessian (1/64) 4
    (observable_selfConcordant_source base hb f D hgzero hH) m ratio hm hr hlower hupper
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

end
end krylov.Convergence
