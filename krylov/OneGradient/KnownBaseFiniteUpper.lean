import krylov.OneGradient.KnownBaseSourceUpper
import krylov.OneGradient.KnownBaseBudgetConversion
import krylov.OneGradient.InformedConstantScaling
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), original all-scenario finite informed bound.
Use: original own-base individual budgets give the sharp known-base
coefficient with a common explicit vanishing inflation and cubic loss.
Source: genuine full physical source upper tube, exact budget conversion
and the proved original informed constant homogeneity/monotonicity.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset krylov.Reference krylov.Secant krylov.Information
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- One common radius and cubic constant bound the actual informed S
output on every original own-base admissible physical source. The leading
coefficient is exactly K_X(c), with explicit factor (1+c*t)^2 tending to
one. No source-path, policy-limit, rank or output-size premise is imposed.
Use: supplies the full original source-wide upper bound before its true
own-base metric and penultimate-error normalization transfer.
Article: main_krylov, thm:local(b), all-scenario informed finite upper bound.
Proof: the whole actual source parameter norm is at most H*t uniformly.
The genuine common physical upper tube applies to every actual source.
Known-metric budget conversion inflates query/output forms by 1+c*t;
exact informed homogeneity and prior monotonicity retain K_X(c). The
actual common cube remainder is at most C*H^3*t^3. -/
theorem knownBase_informed_finite_upper_basis (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef) (hn : 0<n)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    ∃ delta C : ℝ,0<delta ∧ 0<C ∧ ∀ (omega : ℕ → ℝ) (w c : ℝ),
      (∀ l<n,0≤omega l) → 0≤w → 0≤c →
      let W := ∑ l∈range n,omega l
      let H := 1+c+(1+c)*(W+w)
      ∀ t : ℝ,0≤t → t≤1 → c*t<1 → H*t<delta →
      ∀ S : Scenario (n+1),S.Admissible n base (c*t) (fun l => omega l*t) (w*t) 0 →
        ‖cgOperator (metricRoot base)⁻¹ (informedScenarioOutput directions base g S)‖≤
          ‖cgCanonicalError base g n‖*((1+c*t)^2*t^2*informedConstant W w c)+C*H^3*t^3 := by
  obtain ⟨delta,C,hd,hC,hupper⟩ := knownBase_full_source_upper_tube_basis directions base hb hn g hc
  refine ⟨delta,C,hd,hC,?_⟩
  intro omega w c homega hw hc0
  let W := ∑ l∈range n,omega l
  let H := 1+c+(1+c)*(W+w)
  dsimp only
  intro t ht ht1 hct hsmall S hS
  let Theta := knownBaseSourceParameters base hb S hS.1.1.isSymm
    (fun l hl => (hS.2.2.1 l hl).1) hS.2.2.2.1
  have hTheta : ‖Theta‖≤H*t := knownBase_admissible_parameter_norm base hb S omega homega w c t hw hc0 ht ht1 hct hS
  have hbudget := knownBase_admissible_known_budgets base hb S omega homega w c t hw hc0 ht hct hS
  have h := hupper S hS.1.1.isSymm (fun l hl => (hS.2.2.1 l hl).1) hS.2.2.2.1
    (hTheta.trans_lt hsmall) (fun l => (1+c*t)*(omega l*t)) ((1+c*t)*(w*t)) (c*t)
    hbudget.1 hbudget.2 hS.2.1
  have hW : 0≤W := sum_nonneg (fun l hl => homega l (mem_range.mp hl))
  have hsum : (∑ l∈range n,(1+c*t)*(omega l*t))=t*((1+c*t)*W) := by
    rw [← mul_sum,← sum_mul]
    dsimp only [W]
    ring
  have hconstant : informedConstant (∑ l∈range n,(1+c*t)*(omega l*t)) ((1+c*t)*(w*t)) (c*t)≤
      (1+c*t)^2*t^2*informedConstant W w c := by
    have hscale : informedConstant (t*((1+c*t)*W)) (t*((1+c*t)*w)) (c*t)=
        t^2*informedConstant ((1+c*t)*W) ((1+c*t)*w) c := by
      simpa only [mul_comm c t] using informedConstant_scale ((1+c*t)*W) ((1+c*t)*w) c t ht
    rw [hsum,show (1+c*t)*(w*t)=t*((1+c*t)*w) by ring,hscale]
    have hlead := mul_le_mul_of_nonneg_left (informedConstant_inflated_budgets W w c (1+c*t)
      hW hw hc0 (by nlinarith [mul_nonneg hc0 ht])) (sq_nonneg t)
    exact hlead.trans_eq (by ring)
  have hrem : C*‖Theta‖^3≤C*H^3*t^3 := by
    have hnorm := pow_le_pow_left₀ (norm_nonneg Theta) hTheta 3
    exact (mul_le_mul_of_nonneg_left hnorm hC.le).trans_eq (by ring)
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hconstant (norm_nonneg _)) hrem)

/-- The original S specialization of the common native-basis theorem.
Use: preserve the established step-policy physical source interface.
Article: main_krylov, thm:local(b).
Proof: specialize the shared genuine physical theorem to the S basis. -/
theorem knownBase_informed_finite_upper
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef) (hn : 0<n)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1) :
    ∃ delta C : ℝ,0<delta ∧ 0<C ∧ ∀ (omega : ℕ → ℝ) (w c : ℝ),
      (∀ l<n,0≤omega l) → 0≤w → 0≤c →
      let W := ∑ l∈range n,omega l
      let H := 1+c+(1+c)*(W+w)
      ∀ t : ℝ,0≤t → t≤1 → c*t<1 → H*t<delta →
      ∀ S : Scenario (n+1),S.Admissible n base (c*t) (fun l => omega l*t) (w*t) 0 →
        ‖cgOperator (metricRoot base)⁻¹ (informedScenarioOutput false base g S)‖≤
          ‖cgCanonicalError base g n‖*((1+c*t)^2*t^2*informedConstant W w c)+C*H^3*t^3  := by
  exact knownBase_informed_finite_upper_basis false base hb hn g hc

end
end krylov.OneGradient
