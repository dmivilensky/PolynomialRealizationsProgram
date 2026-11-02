import krylov.OneGradient.KnownBaseOwnRisk
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), original whole-source asymptotic upper bound.
Use: obtain the genuine sharp informed source-wide guarantee in the
actual own-base metric and own penultimate reference normalization.
Source: derived common finite all-source risk inequality and actual real
filter limits; source matrices may vary arbitrarily with the scale.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset Filter Topology krylov.Reference krylov.Secant krylov.Information krylov.Stability
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The original actual known-base normalized source output ratio.
Use: its metric and denominator are the true unknown source base, and
its output comes from the actual source-oracle native executor.
Article: main_krylov, thm:local, original varkappa scenario ratio. -/
def informedSourceRisk (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (g : EuclideanSpace ℝ (Fin (n+1)))
    (S : Scenario (n+1)) (t : ℝ) : ℝ :=
  ‖cgOperator (metricRoot S.base)⁻¹ (informedScenarioOutput directions base g S)‖/
    (t^2*‖cgCanonicalError S.base g n‖)

/-- An original source-wide limiting risk guarantee. The same positive
scale neighborhood controls every original admissible physical source,
including arbitrary discontinuous or scale-dependent choices of matrices.
Use: express the original worst limiting coefficient without imposing
a source path, a reference frame or an output-size assumption.
Article: main_krylov, thm:local(b), whole original asymptotic source guarantee. -/
def knownBaseAsymptoticRiskBound (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (g : EuclideanSpace ℝ (Fin (n+1)))
    (omega : ℕ → ℝ) (w c v : ℝ) : Prop :=
  ∀ epsilon : ℝ,0<epsilon → ∀ᶠ t in 𝓝[>] (0 : ℝ),
    ∀ S : Scenario (n+1),S.Admissible n base (c*t) (fun l => omega l*t) (w*t) 0 →
      informedSourceRisk directions base g S t≤v+epsilon

/-- The genuine common finite-risk upper function, retaining every
explicit metric, normalization and cubic full-source loss.
Use: it is independent of the unknown physical scenario at each scale.
Article: main_krylov, thm:local(b), explicit common source risk majorant. -/
def informedRiskUpper (sigma W w c C D t : ℝ) : ℝ :=
  let H := 1+c+(1+c)*(W+w)
  (sigma*(1+c*t)^2*informedConstant W w c+C*H^3*t)/
    ((1-c*t)*(sigma-D*H*t))

/-- The true common all-source risk majorant tends to exactly K_X(c)
at zero scale whenever the actual reference normalization is nonzero.
Use: finite metric/normalization losses preserve the original sharp limit.
Article: main_krylov, thm:local(b), actual limiting informed upper coefficient.
Proof: all real numerator/denominator fields are polynomial in scale;
the genuine denominator at zero is sigma, and exact division cancels it. -/
theorem informedRiskUpper_tendsto (sigma W w c C D : ℝ) (hsigma : sigma≠0) :
    Tendsto (informedRiskUpper sigma W w c C D) (𝓝 0) (𝓝 (informedConstant W w c)) := by
  have hden : (1-c*0)*(sigma-D*(1+c+(1+c)*(W+w))*0)≠0 := by simpa only [mul_zero,sub_zero,one_mul] using hsigma
  have hcont : ContinuousAt (informedRiskUpper sigma W w c C D) 0 := by
    unfold informedRiskUpper
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact hden
  simpa only [informedRiskUpper,mul_zero,add_zero,sub_zero,one_pow,mul_one,zero_add,one_mul,
    mul_div_cancel_left₀ _ hsigma] using hcont.tendsto

/-- The actual original informed S method has the sharp K_X(c)
asymptotic upper guarantee on the full original physical source class.
The guarantee is common before all unknown sources and profiles, in the
actual own-base output metric and own penultimate reference normalization.
Use: original known-base upper quantifiers permit arbitrary source choices
at every shrinking scale; no smooth-family restriction remains.
Article: main_krylov, thm:local(b), original full-source informed upper bound.
Proof: choose the genuine common finite-risk tube and actual reference
normalization. Its explicit upper function tends to K_X(c). All real tube
and denominator conditions hold on one positive scale neighborhood, before
every physical scenario. Apply the true all-source finite risk inequality. -/
theorem knownBase_informed_asymptotic_upper_basis (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef) (hn : 0<n)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (omega : ℕ → ℝ) (homega : ∀ l<n,0≤omega l) (w c : ℝ) (hw : 0≤w) (hc0 : 0≤c) :
    knownBaseAsymptoticRiskBound directions base g omega w c (informedConstant (∑ l∈range n,omega l) w c) := by
  obtain ⟨delta,C,D,hd,hC,hD,hbound⟩ := knownBase_informed_own_risk_bound_basis directions base hb hn g hc
  let W := ∑ l∈range n,omega l
  let H := 1+c+(1+c)*(W+w)
  let sigma := ‖cgCanonicalError base g n‖
  have hsigma : 0<sigma := canonical_error_pos base hb (CG.gradient (cgOperator base) g n) (cg_nonstagnation base hb g n (by omega))
  have hlimit := informedRiskUpper_tendsto sigma W w c C D hsigma.ne'
  have hlin (a b : ℝ) (hb0 : 0<b) : ∀ᶠ t : ℝ in 𝓝 0,a*t<b := by
    have ht : Tendsto (fun t : ℝ => a*t) (𝓝 0) (𝓝 0) := by
      simpa only [id_eq,mul_zero] using (tendsto_const_nhds (x := a)).mul (tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 0) (𝓝 0))
    exact ht.eventually (gt_mem_nhds hb0)
  intro epsilon hepsilon
  have hvalue : ∀ᶠ t in 𝓝 (0 : ℝ),informedRiskUpper sigma W w c C D t< informedConstant W w c+epsilon :=
    hlimit.eventually (gt_mem_nhds (by linarith))
  have hnear : ∀ᶠ t : ℝ in 𝓝 0,t<1 ∧ c*t<1 ∧ H*t<delta ∧ D*H*t<sigma ∧
      informedRiskUpper sigma W w c C D t< informedConstant W w c+epsilon := by
    filter_upwards [hlin 1 1 (by norm_num),hlin c 1 (by norm_num),hlin H delta hd,hlin (D*H) sigma hsigma,hvalue]
      with t ht hct hH hden hv
    exact ⟨by simpa only [one_mul] using ht,hct,hH,hden,hv⟩
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with t ht htpos
  intro S hS
  have hrisk : informedSourceRisk directions base g S t≤ informedRiskUpper sigma W w c C D t :=
    hbound omega w c homega hw hc0 t htpos ht.1.le ht.2.1 ht.2.2.1 ht.2.2.2.1 S hS
  exact hrisk.trans ht.2.2.2.2.le

/-- The original S specialization of the common native-basis theorem.
Use: preserve the established step-policy physical source interface.
Article: main_krylov, thm:local(b).
Proof: specialize the shared genuine physical theorem to the S basis. -/
theorem knownBase_informed_asymptotic_upper
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef) (hn : 0<n)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (omega : ℕ → ℝ) (homega : ∀ l<n,0≤omega l) (w c : ℝ) (hw : 0≤w) (hc0 : 0≤c) :
    knownBaseAsymptoticRiskBound false base g omega w c (informedConstant (∑ l∈range n,omega l) w c)  := by
  exact knownBase_informed_asymptotic_upper_basis false base hb hn g hc omega homega w c hw hc0

end
end krylov.OneGradient
