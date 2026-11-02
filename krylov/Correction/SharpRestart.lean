import krylov.Correction.SharpRestartEnergy

/-!
Article: main_krylov, apG:restart, complete sharp observed restart lemma.
Use: derive the original constants from true normalized Gram conditioning,
actual measured conjugacy and the real old-span direction equation.
Source: the proved sharp projection and positive-root energy lemmas.
The short-step displacement is explicitly canonical, correcting the
source's missing H_*^(1/2) in that norm.
-/
namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability krylov.Secant
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n p : ℕ}

/-- The original measured-error smallness gives the exact projected
fraction used in the sharp restart energy proof. Article: apG:restart. -/
theorem sharp_restart_projection_fraction (s y : Fin p → EuclideanSpace ℝ (Fin n))
    (hgram : ∀ i,(3/4 : ℝ)≤(crossGram_isHermitian s).eigenvalues i)
    (d : EuclideanSpace ℝ (Fin n)) (r epsilon : ℝ) (hr : 1≤r) (he : 0≤epsilon)
    (hsmall : Real.sqrt p*epsilon≤Real.sqrt 3/(8*r^2))
    (hy : ∀ i,‖y i-s i‖≤epsilon/2) (ho : ∀ i,inner ℝ (y i) d=0) :
    8*r^2*‖observedProjection s d‖≤‖d‖ := by
  have hh := observedProjection_sharp_conjugacy s y hgram d he hy ho
  have hr2 : 0<8*r^2 := by positivity
  have hb := (le_div_iff₀ hr2).mp hsmall
  have hs : 0<Real.sqrt 3 := by positivity
  have hcoef : 8*r^2*((Real.sqrt p/Real.sqrt 3)*epsilon)≤1 := by
    apply (mul_le_mul_iff_left₀ hs).mp
    calc
      _ = (Real.sqrt p*epsilon)*(8*r^2) := by field_simp
      _ ≤ _ := by simpa only [one_mul] using hb
  have hmul := mul_le_mul_of_nonneg_left hh hr2.le
  have hnorm := mul_le_mul_of_nonneg_right hcoef (norm_nonneg d)
  nlinarith only [hmul,hnorm]

/-- The original non-descent estimate with its exact printed constant.
The direction span and all conjugacy pairings are the actual ones from
the observed solve, rather than an assumed energy or rate estimate.
Article: main_krylov, apG:restart(a). -/
theorem sharp_observed_nondescent (s y : Fin p → EuclideanSpace ℝ (Fin n))
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (g d : EuclideanSpace ℝ (Fin n)) (m r epsilon : ℝ) (hm : 0<m) (hr : 1≤r)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n),m^2*‖v‖^2≤ inner ℝ v (cgOperator H v))
    (hupper : ‖cgOperator H‖≤m^2*r^2)
    (hgram : ∀ i,(3/4 : ℝ)≤(crossGram_isHermitian s).eigenvalues i)
    (he : 0≤epsilon) (hsmall : Real.sqrt p*epsilon≤Real.sqrt 3/(8*r^2))
    (hy : ∀ i,‖y i-s i‖≤epsilon/2) (ho : ∀ i,inner ℝ (y i) d=0)
    (hspan : d+cgOperator H g∈Submodule.span ℝ (Set.range s)) (hslope : 0≤ inner ℝ g d) :
    ‖g‖≤2*(1+r)*‖observedProjection s g‖ := by
  have hp := sharp_restart_projection_fraction s y hgram d r epsilon hr he hsmall hy ho
  obtain ⟨hg,_hd,henergy⟩ := restart_normalized_energy s H hH g d m r hm hr hlower hupper hspan hp
  have hs : (-inner ℝ g d)/m^2≤0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg m)
  exact sharp_nondescent_scalar (norm_nonneg _) hr hg (henergy.trans (by linarith))

/-- The original short-step estimate with exact constant 4 kappa.
The actual new quadratic has norm <=9/8 in canonical coordinates and
the actual exact-search identity is the only line-step assumption.
Article: main_krylov, apG:restart(b), canonical displacement norm. -/
theorem sharp_observed_short_step (s y : Fin p → EuclideanSpace ℝ (Fin n))
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.PosDef)
    (g d : EuclideanSpace ℝ (Fin n)) (m r epsilon alpha : ℝ) (hm : 0<m) (hr : 1≤r)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n),m^2*‖v‖^2≤ inner ℝ v (cgOperator H v))
    (hupper : ‖cgOperator H‖≤m^2*r^2)
    (hgram : ∀ i,(3/4 : ℝ)≤(crossGram_isHermitian s).eigenvalues i)
    (he : 0≤epsilon) (hsmall : Real.sqrt p*epsilon≤Real.sqrt 3/(8*r^2))
    (hy : ∀ i,‖y i-s i‖≤epsilon/2) (ho : ∀ i,inner ℝ (y i) d=0)
    (hspan : d+cgOperator H g∈Submodule.span ℝ (Set.range s))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ‖A‖≤(9/8 : ℝ)) (halpha : 0<alpha)
    (hline : -inner ℝ g d=alpha*inner ℝ d (A d)) :
    ‖g‖≤4*r^2*(‖observedProjection s g‖+alpha*‖d‖) := by
  have hp := sharp_restart_projection_fraction s y hgram d r epsilon hr he hsmall hy ho
  obtain ⟨hg,hd,henergy⟩ := restart_normalized_energy s H hH g d m r hm hr hlower hupper hspan hp
  let a := observedProjection s g
  let z := ‖cgOperator (metricRoot H) (g-a)‖/m
  have hcurv : inner ℝ d (A d)≤(9/8 : ℝ)*‖d‖^2 := by
    have hh := real_inner_le_norm d (A d)
    have hn := (A.le_opNorm d).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg d))
    nlinarith only [hh,mul_le_mul_of_nonneg_left hn (norm_nonneg d)]
  have hslope : -inner ℝ g d≤(9/4 : ℝ)*m^2*r^2*(alpha*‖d‖)*(‖a‖+z) := by
    have hh := mul_le_mul_of_nonneg_left hcurv halpha.le
    have hdn := mul_le_mul_of_nonneg_left hd (by positivity : 0≤(9/8 : ℝ)*alpha*‖d‖)
    have hgn := mul_le_mul_of_nonneg_left hg (by positivity : 0≤(9/4 : ℝ)*m^2*r^2*(alpha*‖d‖))
    rw [←hline] at hh
    nlinarith only [hh,hdn,hgn]
  have hdiv : (-inner ℝ g d)/m^2≤(9/4 : ℝ)*r^2*(alpha*‖d‖)*(‖a‖+z) := by
    apply (div_le_iff₀ (sq_pos_of_pos hm)).mpr
    nlinarith only [hslope]
  apply sharp_short_step_scalar (norm_nonneg a) (by positivity : 0≤alpha*‖d‖) hr rfl hg
  change z^2≤_ at henergy ⊢
  nlinarith only [henergy,hdiv]

end
end krylov.Correction
