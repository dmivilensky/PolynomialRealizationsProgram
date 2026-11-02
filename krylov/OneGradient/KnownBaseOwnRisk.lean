import krylov.OneGradient.KnownBaseFiniteUpper
import krylov.OneGradient.KnownBaseReferenceNorm
import krylov.Information.MetricComparison
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), actual own-normalized full-source risk.
Use: the original physical source output ratio has an explicit common
upper function tending to the source informed constant K_X(c).
Source: actual all-scenario finite upper bound, genuine own-base metric
comparison and proved common actual penultimate-reference normalization.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset krylov.Reference krylov.Secant krylov.Information
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual source-own inverse-root metric costs at most the exact
factor (1-r)^(-1) on every true physical output when its original known
prior radius is r<1.
Use: all-source upper estimates retain the actual own-base output metric.
Article: main_krylov, thm:local(b), genuine full-source own-metric comparison.
Proof: the real signed prior displacement gives (1-r)*A≤B. Its positive
inverse scalar gives A≤(1-r)^(-1)*B; reuse the proved actual dual-norm
comparison for the same physical vector in its two true metrics. -/
theorem knownBase_prior_dual_norm_bound
    (A B : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef) (hB : B.PosDef)
    (r : ℝ) (hr : 0≤r) (hr1 : r<1) (hprior : relativeBudget A (B-A)≤r)
    (v : EuclideanSpace ℝ (Fin (n+1))) :
    ‖cgOperator (metricRoot B)⁻¹ v‖≤(1-r)⁻¹*‖cgOperator (metricRoot A)⁻¹ v‖ := by
  have ha : 0<1-r := by linarith
  have hlower := (relative_displacement_base A B hA hB.1.isSymm hr hr1 hprior).1
  have hupper : A≤(1-r)⁻¹ • B := by
    have h := smul_le_smul_of_nonneg_left hlower (inv_nonneg.mpr ha.le)
    simpa only [smul_smul,inv_mul_cancel₀ ha.ne',one_smul] using h
  have hfactor : 1≤(1-r)⁻¹ := by
    apply (one_le_inv₀ ha).mpr
    linarith
  exact dual_norm_le_of_base_upper B A hB hA hfactor hupper v

/-- Every original admissible physical source has its actual normalized
informed S output bounded by one explicit common risk function. Both the
output metric and penultimate error denominator are the source's own true
base quantities, with no source path or scenario regularity hypothesis.
Use: the common upper function tends to K_X(c), giving the original
whole-source asymptotic informed guarantee with the exact normalization.
Article: main_krylov, thm:local(b), genuine own-normalized all-source bound.
Proof: common finite source and actual normalization tubes are chosen
before every source and profile. The true parameter norm is at most H*t.
The original prior metric costs (1-c*t)^(-1), while the actual denominator
is at least sigma-D*H*t. Divide the proved positive real inequalities and
cancel the true scale squared, retaining all explicit finite losses. -/
theorem knownBase_informed_own_risk_bound_basis (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef) (hn : 0<n)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    ∃ delta C D : ℝ,0<delta ∧ 0<C ∧ 0<D ∧ ∀ (omega : ℕ → ℝ) (w c : ℝ),
      (∀ l<n,0≤omega l) → 0≤w → 0≤c →
      let W := ∑ l∈range n,omega l
      let H := 1+c+(1+c)*(W+w)
      let sigma := ‖cgCanonicalError base g n‖
      ∀ t : ℝ,0<t → t≤1 → c*t<1 → H*t<delta → D*H*t<sigma →
      ∀ S : Scenario (n+1),S.Admissible n base (c*t) (fun l => omega l*t) (w*t) 0 →
        ‖cgOperator (metricRoot S.base)⁻¹ (informedScenarioOutput directions base g S)‖/
          (t^2*‖cgCanonicalError S.base g n‖)≤
          (sigma*(1+c*t)^2*informedConstant W w c+C*H^3*t)/
            ((1-c*t)*(sigma-D*H*t)) := by
  obtain ⟨delta0,C,hd0,hC,hfinite⟩ := knownBase_informed_finite_upper_basis directions base hb hn g hc
  obtain ⟨delta1,D,hd1,hD,hnorm⟩ := knownBase_source_reference_norm_tube base hb hn g hc
  refine ⟨min delta0 delta1,C,D,lt_min hd0 hd1,hC,hD,?_⟩
  intro omega w c homega hw hc0
  let W := ∑ l∈range n,omega l
  let H := 1+c+(1+c)*(W+w)
  let sigma := ‖cgCanonicalError base g n‖
  dsimp only
  intro t ht ht1 hct hsmall hden S hS
  let Theta := knownBaseSourceParameters base hb S hS.1.1.isSymm
    (fun l hl => (hS.2.2.1 l hl).1) hS.2.2.2.1
  let out := informedScenarioOutput directions base g S
  let a := 1-c*t
  let b := sigma-D*H*t
  let own := ‖cgCanonicalError S.base g n‖
  let Q := sigma*(1+c*t)^2*informedConstant W w c+C*H^3*t
  have ha : 0<a := by dsimp only [a];linarith
  have hb0 : 0<b := by dsimp only [b];linarith
  have hTheta : ‖Theta‖≤H*t := knownBase_admissible_parameter_norm base hb S omega homega w c t
    hw hc0 ht.le ht1 hct hS
  have htube := hnorm S hS.1.1.isSymm (fun l hl => (hS.2.2.1 l hl).1) hS.2.2.2.1
    (hTheta.trans_lt (hsmall.trans_le (min_le_right _ _)))
  have hlow : b≤own := by
    have hvariation := (abs_le.mp htube).1
    have hprod := mul_le_mul_of_nonneg_left hTheta hD.le
    dsimp only [b,own,sigma]
    nlinarith
  have hown : 0<own := hb0.trans_le hlow
  have hknown : ‖cgOperator (metricRoot base)⁻¹ out‖≤t^2*Q := by
    have h := hfinite omega w c homega hw hc0 t ht.le ht1 hct
      (hsmall.trans_le (min_le_left _ _)) S hS
    exact h.trans_eq (by dsimp only [Q,sigma,W,H];ring)
  have hmetric := knownBase_prior_dual_norm_bound base S.base hb hS.1 (c*t)
    (mul_nonneg hc0 ht.le) hct hS.2.1 out
  have hphysical : ‖cgOperator (metricRoot S.base)⁻¹ out‖≤a⁻¹*(t^2*Q) :=
    hmetric.trans (mul_le_mul_of_nonneg_left hknown (inv_nonneg.mpr ha.le))
  have hnum : 0≤a⁻¹*(t^2*Q) := (norm_nonneg _).trans hphysical
  have hratio : ‖cgOperator (metricRoot S.base)⁻¹ out‖/own≤(a⁻¹*(t^2*Q))/b := by
    apply (div_le_div_of_nonneg_right hphysical hown.le).trans
    apply (div_le_div_iff₀ hown hb0).mpr
    exact mul_le_mul_of_nonneg_left hlow hnum
  have heq : (a⁻¹*(t^2*Q))/b=(Q/(a*b))*t^2 := by field_simp
  have hresult : (‖cgOperator (metricRoot S.base)⁻¹ out‖/own)/t^2≤Q/(a*b) := by
    apply (div_le_iff₀ (sq_pos_of_pos ht)).mpr
    exact hratio.trans_eq heq
  simpa only [div_div,mul_comm own (t^2)] using hresult

/-- The original S specialization of the common native-basis theorem.
Use: preserve the established step-policy physical source interface.
Article: main_krylov, thm:local(b).
Proof: specialize the shared genuine physical theorem to the S basis. -/
theorem knownBase_informed_own_risk_bound
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef) (hn : 0<n)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    ∃ delta C D : ℝ,0<delta ∧ 0<C ∧ 0<D ∧ ∀ (omega : ℕ → ℝ) (w c : ℝ),
      (∀ l<n,0≤omega l) → 0≤w → 0≤c →
      let W := ∑ l∈range n,omega l
      let H := 1+c+(1+c)*(W+w)
      let sigma := ‖cgCanonicalError base g n‖
      ∀ t : ℝ,0<t → t≤1 → c*t<1 → H*t<delta → D*H*t<sigma →
      ∀ S : Scenario (n+1),S.Admissible n base (c*t) (fun l => omega l*t) (w*t) 0 →
        ‖cgOperator (metricRoot S.base)⁻¹ (informedScenarioOutput false base g S)‖/
          (t^2*‖cgCanonicalError S.base g n‖)≤
          (sigma*(1+c*t)^2*informedConstant W w c+C*H^3*t)/
            ((1-c*t)*(sigma-D*H*t))  := by
  exact knownBase_informed_own_risk_bound_basis false base hb hn g hc

end
end krylov.OneGradient
