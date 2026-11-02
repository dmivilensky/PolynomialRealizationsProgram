import krylov.Convergence.ObservableSelfConcordant

/-!
Article: main_krylov, apG:Dunif, absolute observable FC constant.
Use: state the complete actual-function result with an explicit universal
radius depending only on dimension and a true spectral condition bound.
Source: the proved scalar self-concordant source theorem and complete
first-stopping FC estimate. No compact reference or (N) is assumed.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Functions krylov.Nonlinear krylov.Reference
open scoped InnerProductSpace NNReal
variable {n : ℕ}

/-- Explicit dimension/condition-only radius for the real observable
FC cycle; ratio is the square root of the condition bound.
Article: main_krylov, apG:Dunif. -/
def observableFCRadius (n : ℕ) (ratio : ℝ) : ℝ := 1/(8192*(n:ℝ)*ratio^2)

/-- The explicit radius supplies every real local analytic allowance
before choosing the scalar function. Article: main_krylov, apG:Dunif. -/
theorem observable_fc_radius_budgets (hn : 1≤n) (ratio e : ℝ) (hr : 1≤ratio)
    (he : 0≤e) (hsize : e≤observableFCRadius n ratio) :
    0<observableFCRadius n ratio ∧ e<(1/64:ℝ)/4 ∧
      (n:ℝ)*(2*(4:ℝ)*e)≤1/8 ∧
      Real.sqrt n*(4*(4:ℝ)*e)≤Real.sqrt 3/(8*ratio^2) := by
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hr2 : 1≤ratio^2 := by nlinarith only [hr,sq_nonneg (ratio-1)]
  have hden : 0<8192*(n:ℝ)*ratio^2 := by positivity
  have hb : e*(8192*(n:ℝ)*ratio^2)≤1 := (le_div_iff₀ hden).mp hsize
  have hnr : 1≤(n:ℝ)*ratio^2 := by nlinarith only [hn',hr2,mul_nonneg (sub_nonneg.mpr hn') (sub_nonneg.mpr hr2)]
  have hnrE := mul_le_mul_of_nonneg_right hnr he
  have hnE := mul_le_mul_of_nonneg_right hr2 (show 0≤(n:ℝ)*e by positivity)
  have he8192 : e≤1/8192 := by nlinarith only [hb,hnrE]
  have hne8192 : (n:ℝ)*e≤1/8192 := by nlinarith only [hb,hnE]
  have hroot : Real.sqrt n≤n := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith only [hn']⟩
  refine ⟨by dsimp only [observableFCRadius];positivity,by norm_num at he8192 ⊢;linarith,?_,?_⟩
  · nlinarith only [hne8192]
  · apply (le_div_iff₀ (by positivity : 0<8*ratio^2)).mpr
    have hh := mul_le_mul_of_nonneg_right hroot (show 0≤4*(4:ℝ)*e by positivity)
    have hh' := mul_le_mul_of_nonneg_right hh (show 0≤8*ratio^2 by positivity)
    have hbound : (Real.sqrt n*(4*(4:ℝ)*e))*(8*ratio^2)≤1/64 := by
      nlinarith only [hh',hb]
    exact hbound.trans (Real.le_sqrt_of_sq_le (by norm_num))

/-- On every genuine standard-self-concordant scalar function, the
literal observable FC cycle obeys the printed uniform quadratic order,
with absolute constant 1024 and a radius fixed before the function.
For exact spectral endpoints ratio is sqrt(kappa).
Article: main_krylov, apG:Dunif, complete FC source theorem. -/
theorem observable_fc_uniform_selfConcordant
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (hn : 1≤n)
    (m ratio : ℝ) (hm : 0<m) (hr : 1≤ratio)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n),m^2*‖v‖^2 ≤ inner ℝ v (cgOperator base v))
    (hupper : ‖cgOperator base‖≤m^2*ratio^2)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (D : StandardSelfConcordantData f Set.univ)
    (hgzero : gradient f 0=0) (hH : D.hessian 0=cgOperator base)
    (bar : ℝ) (x₀ : EuclideanSpace ℝ (Fin n))
    (hx₀ : ‖metricCoordinates base hb x₀‖≤observableFCRadius n ratio) :
    ‖metricCoordinates base hb (observableRestartPoint false bar (metricCoordinates base hb)
      f (gradient f) (1/64) n x₀)‖≤
      1024*(1+ratio)*(n:ℝ)*Real.sqrt n*‖metricCoordinates base hb x₀‖^2 := by
  obtain ⟨_hpos,hstart,hsmall,hsharp⟩ := observable_fc_radius_budgets hn ratio _ hr (norm_nonneg _) hx₀
  have hh := observable_fc_actual_cycle_bound base hb f (gradient f) D.hessian (1/64) 4
    (observable_selfConcordant_source base hb f D hgzero hH) m ratio hm hr hlower hupper
    bar x₀ hstart hsmall hsharp
  simpa only [NNReal.coe_ofNat,show (256:ℝ)*4=1024 by norm_num] using hh

end
end krylov.Convergence
