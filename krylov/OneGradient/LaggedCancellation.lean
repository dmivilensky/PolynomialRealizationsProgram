import krylov.OneGradient.LaggedSmooth
import krylov.OneGradient.XRFCStepTaylor
import krylov.OneGradient.XRFCDirectionTaylor
import krylov.Reference.HeavyBallMeasure
set_option autoImplicit false
/-!
Article: main_krylov, prop:hb(a), actual lagged heavy-ball cancellation.
Use: arbitrary positive first trials give zero genuine amplitudes in both
bases, and hence a true quadratic semantic-output remainder.
Source: actual measured previous CG lengths, original chronological amplitude
products, the true heavy-ball spectral-measure dictionary and native Taylor bounds.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix chebyshev1 krylov.Methods krylov.Reference krylov.Stability krylov.Envelope krylov.Secant
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every actual lagged trial after initialization is exact when the true
reference CG lengths are constant, in either source basis.
Use: the arbitrary initial trial is retained without an exact-search premise.
Article: main_krylov, prop:hb(a).
Proof: the actual source step-history measurement is the previous CG length. -/
theorem lagged_constant_trial (directions : Bool) {tau0 : ℝ} (htau0 : 0<tau0)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n)
    (alpha : ℝ) (halpha : ∀ i<n,CG.length (cgOperator base) g i=alpha)
    (k : ℕ) (hk : 0<k) (hkn : k<n) :
    let trial := laggedTrial directions tau0
    trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g k)=
      CG.length (cgOperator base) g k := by
  have hp := cgOperator_positive base hb
  have h := lagged_trial_step_reference_next directions htau0 (cgOperator base) hp.1 hp.2 g n
    (fun i hi => cg_nonstagnation base hb g i (by rw [hc];exact hi)) (k-1) (by omega)
  rw [Nat.sub_add_cancel hk,halpha (k-1) (by omega),← halpha k hkn] at h
  exact h

/-- All genuine full-cycle lagged amplitudes vanish on constant-length
references of dimension at least two, including the arbitrary first miss.
Use: both true XRFC response maps cancel for every perturbation family.
Article: main_krylov, prop:hb(a), a_l=0.
Proof: every positive-age missed line is zero. The first-age amplitude has
the exact second trial as a genuine later zero factor in its true product. -/
theorem lagged_constant_coefficient (directions : Bool) {tau0 : ℝ} (htau0 : 0<tau0)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n) (hn : 2≤n)
    (alpha : ℝ) (halpha : ∀ i<n,CG.length (cgOperator base) g i=alpha)
    (l : ℕ) (hl : l<n) : xrfcTrialCoefficient (laggedTrial directions tau0) base g n l=0 := by
  let trial : History (EuclideanSpace ℝ (Fin n)) → ℝ := laggedTrial directions tau0
  by_cases hl0 : l=0
  · subst l
    rw [xrfcTrialCoefficient_printed trial base hb g n 0 (by omega)]
    dsimp only
    have hprod : (∏ j∈Finset.Ico (0+1) n,
        (CG.length (cgOperator base) g j-
          trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g j))/
            trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g j))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_Ico.mpr ⟨le_rfl,show 1<n by omega⟩)
      have he : trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g 1)=
          CG.length (cgOperator base) g 1 :=
        lagged_constant_trial directions htau0 base hb g hc alpha halpha 1 (by omega) (by omega)
      rw [he,sub_self,zero_div]
    rw [hprod,mul_zero,zero_mul]
  · exact xrfcTrialCoefficient_exact trial base g n l
      (lagged_constant_trial directions htau0 base hb g hc alpha halpha l (by omega) hl)

/-- Both original actual response maps vanish for the genuine lagged rule
on constant-length references, even if the initial trial is arbitrarily inexact.
Use: the native semantic Taylor bounds therefore have zero linear term.
Article: main_krylov, prop:hb(a).
Proof: the proved original full-cycle amplitudes vanish term by term. -/
theorem lagged_constant_responses (directions : Bool) {tau0 : ℝ} (htau0 : 0<tau0)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n) (hn : 2≤n)
    (alpha : ℝ) (halpha : ∀ i<n,CG.length (cgOperator base) g i=alpha)
    (E : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    xrfcDirectionResponse (laggedTrial directions tau0) base g E=0 ∧
      xrfcStepResponse (laggedTrial directions tau0) base g E=0 := by
  have hz (i : ℕ) (hi : i∈Finset.range n) := lagged_constant_coefficient directions htau0
    base hb g hc hn alpha halpha i (Finset.mem_range.mp hi)
  constructor
  · exact Finset.sum_eq_zero (fun i hi => by rw [hz i hi,zero_smul])
  · exact Finset.sum_eq_zero (fun i hi => by rw [hz i hi,zero_smul])

/-- The actual native lagged method has a genuine quadratic output error
on every smooth varying prefix and output-operator path at a constant-length
reference. Its trial regularity is proved, not an additional hypothesis.
Use: covers both original bases and arbitrary positive initial trials.
Article: main_krylov, prop:hb(a).
Proof: genuine lagged trial charts supply the native C-two hypotheses; all
actual measured response coefficients cancel in the proved output expansion. -/
theorem lagged_constant_output_quadratic (directions : Bool) {tau0 : ℝ} (htau0 : 0<tau0)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hc : referenceAtomCount base hb g=n) (hn : 2≤n)
    (alpha : ℝ) (halpha : ∀ i<n,CG.length (cgOperator base) g i=alpha)
    (A : ℝ → ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ k,ContDiffAt ℝ 2 (fun t => A t k) 0)
    (hsym : ∀ t k,(A t k).IsSymm) (hA0 : ∀ k,A 0 k=base) :
    let method := xrfcBasisMethod directions (laggedTrial directions tau0)
    let op := fun t k => cgOperator (A t k)
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ t : ℝ,|t|≤delta →
      ‖cgOperator (metricRoot base)⁻¹
        (method.outputGradient (op t n) (oneGradientRun method (op t) g n))‖≤C*t^2 := by
  have hp := cgOperator_positive base hb
  have hpre : ∀ i<n,CG.gradient (cgOperator base) g i≠0 :=
    fun i hi => cg_nonstagnation base hb g i (by rw [hc];exact hi)
  have hT := fun (k : ℕ) (hk : k<n) => lagged_trial_reference_contDiff (r := 2) directions htau0
    (cgOperator base) hp.1 hp.2 g n hpre k (show k≤n from hk.le)
  cases directions with
  | false =>
    obtain ⟨delta,C,hd,hC,hbound⟩ := xrfc_step_output_quadratic_remainder (laggedTrial false tau0)
      base hb g hc (by omega) A hA hsym hA0
      (fun _ _ => (lagged_trial_positive false htau0 _).ne') hT
    refine ⟨delta,C,hd,hC,?_⟩
    intro t ht
    have h := hbound t ht
    rw [(lagged_constant_responses false htau0 base hb g hc hn alpha halpha _).2,
      smul_zero,sub_zero] at h
    exact h
  | true =>
    obtain ⟨delta,C,hd,hC,hbound⟩ := xrfc_direction_output_quadratic_remainder (laggedTrial true tau0)
      base hb g hc (by omega) A hA hA0
      (fun _ _ => (lagged_trial_positive true htau0 _).ne') hT
    refine ⟨delta,C,hd,hC,?_⟩
    intro t ht
    have h := hbound t ht
    rw [(lagged_constant_responses true htau0 base hb g hc hn alpha halpha _).1,
      smul_zero,sub_zero] at h
    exact h

/-- The original heavy-ball spectral-measure references have zero genuine
lagged amplitudes and zero S/D linear responses for arbitrary positive tau0.
Use: the cancellation concerns the article's actual physical measure class.
Article: main_krylov, prop:hb(a).
Proof: the proved original spectral-measure dictionary gives its constant
true CG lengths; apply the actual chronological lagged cancellation. -/
theorem lagged_heavyBall_measure_cancellation (directions : Bool) {tau0 : ℝ} (htau0 : 0<tau0)
    (I : SpectralInterval) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) (hc : referenceAtomCount base hb g=n) (hn : 2≤n)
    (hmeasure : ∀ f,gradientSpectralIntegral base hb g hg f=heavyBallSpectralIntegral I n (by omega) f)
    (E : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (∀ l<n,xrfcTrialCoefficient (laggedTrial directions tau0) base g n l=0) ∧
      xrfcDirectionResponse (laggedTrial directions tau0) base g E=0 ∧
      xrfcStepResponse (laggedTrial directions tau0) base g E=0 := by
  have ha (i : ℕ) (hi : i<n) := (heavyBall_measure_coefficients I (by omega)
    base hb g hg hmeasure i hi).1
  exact ⟨fun l hl => lagged_constant_coefficient directions htau0 base hb g hc hn _ ha l hl,
    lagged_constant_responses directions htau0 base hb g hc hn _ ha E⟩

end
end krylov.OneGradient
