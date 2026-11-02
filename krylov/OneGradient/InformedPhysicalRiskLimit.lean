import krylov.OneGradient.InformedPhysicalMetricSqueeze
import krylov.Stability.QuadraticNormLimit
import krylov.OneGradient.InformedReferenceAttainment
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), true physical informed risk attainment.
Use: the original genuine physical source family attains K_X(c) for the
actual native method in its own metric and true own reference normalization.
Source: actual native physical cubic output, exact original prior
normalization and true physical metric squeeze, with original admissibility.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset Filter Topology krylov.Reference krylov.Secant krylov.Information krylov.Stability
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual informed physical source output has its exact normalized
known-metric limit equal to the norm of its genuine correlated reference
coefficient, with all real zero leading coefficients included.
Use: no normalized output limit is assumed in original physical sharpness.
Article: main_krylov, thm:local(b), actual physical leading risk coefficient.
Proof: apply the real quadratic-output norm-limit theorem to the proved
native cubic physical output. Divide by its true nonzero known penultimate
reference normalization and cancel its actual positive scalar exactly. -/
theorem informedPhysicalScenario_known_risk_tendsto_basis (directions : Bool)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (D : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (R F : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hD : ∀ l<n,(D l).IsSymm) (hF : F.IsSymm) (c : ℝ)
    (hR : cgOperator R=c • InnerProductSpace.rankOne ℝ
      (canonicalCGUnitStep A g n) (canonicalCGUnitStep A g n)) :
    Tendsto (fun t : ℝ => ‖cgOperator (metricRoot A)⁻¹
      (informedScenarioOutput directions A g (informedPhysicalScenario A hA g hg hc D F c t))‖/
        (t^2*‖cgCanonicalError A g n‖)) (𝓝[>] 0) (𝓝 ‖informedReferencePivotCoefficient A g D R F‖) := by
  let v := fun t : ℝ => cgOperator (metricRoot A)⁻¹
    (informedScenarioOutput directions A g (informedPhysicalScenario A hA g hg hc D F c t))
  let V := informedReferencePivotCoefficient A g D R F
  let sigma := ‖cgCanonicalError A g n‖
  have hsigma : 0<sigma := canonical_error_pos A hA (CG.gradient (cgOperator A) g n)
    (cg_nonstagnation A hA g n (by rw [full_gradient_atom_count A hA g hc];omega))
  have h := quadratic_output_norm_tendsto v (sigma • V)
    (informedPhysicalScenario_output_cubic_basis directions A hA g hg hc D R F hD hF c hR)
  have hnorm : ‖sigma • V‖=sigma*‖V‖ := by rw [norm_smul,Real.norm_of_nonneg hsigma.le]
  have hdivide := h.div_const sigma
  simpa only [div_div,hnorm,mul_div_cancel_left₀ _ hsigma.ne'] using hdivide

/-- The original S specialization of the common native-basis theorem.
Use: preserve the established step-policy physical source interface.
Article: main_krylov, thm:local(b).
Proof: specialize the shared genuine physical theorem to the S basis. -/
theorem informedPhysicalScenario_known_risk_tendsto
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (D : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (R F : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hD : ∀ l<n,(D l).IsSymm) (hF : F.IsSymm) (c : ℝ)
    (hR : cgOperator R=c • InnerProductSpace.rankOne ℝ
      (canonicalCGUnitStep A g n) (canonicalCGUnitStep A g n)) :
    Tendsto (fun t : ℝ => ‖cgOperator (metricRoot A)⁻¹
      (informedScenarioOutput false A g (informedPhysicalScenario A hA g hg hc D F c t))‖/
        (t^2*‖cgCanonicalError A g n‖)) (𝓝[>] 0) (𝓝 ‖informedReferencePivotCoefficient A g D R F‖)  := by
  exact informedPhysicalScenario_known_risk_tendsto_basis false A hA g hg hc D R F hD hF c hR

/-- The actual original informed risk on the genuine physical source
family tends to the full correlated reference coefficient norm in its
own metric and true own penultimate-reference normalization.
Use: physical sharpness includes the original source normalization and
does not rely on a fixed-metric surrogate or assumed moving-axis estimate.
Article: main_krylov, thm:local(b), genuine original physical risk limit.
Proof: the actual known-metric normalized risk limit is already derived
from native output. True physical metric and exact prior normalization
squeeze its original own-risk between factors tending to one times that
same known risk. Apply the genuine real filter squeeze theorem. -/
theorem informedPhysicalScenario_own_risk_tendsto_basis (directions : Bool)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (D : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (R F : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hD : ∀ l<n,(D l).IsSymm) (hF : F.IsSymm) (c : ℝ) (hc0 : 0≤c)
    (hR : cgOperator R=c • InnerProductSpace.rankOne ℝ
      (canonicalCGUnitStep A g n) (canonicalCGUnitStep A g n)) :
    Tendsto (fun t : ℝ => informedSourceRisk directions A g (informedPhysicalScenario A hA g hg hc D F c t) t)
      (𝓝[>] 0) (𝓝 ‖informedReferencePivotCoefficient A g D R F‖) := by
  let S := fun t => informedPhysicalScenario A hA g hg hc D F c t
  let known := fun t : ℝ => ‖cgOperator (metricRoot A)⁻¹ (informedScenarioOutput directions A g (S t))‖/
    (t^2*‖cgCanonicalError A g n‖)
  have hknown : Tendsto known (𝓝[>] 0) (𝓝 ‖informedReferencePivotCoefficient A g D R F‖) :=
    informedPhysicalScenario_known_risk_tendsto_basis directions A hA g hg hc D R F hD hF c hR
  have hf : Tendsto (fun t : ℝ => 1+c*t) (𝓝[>] 0) (𝓝 1) := by
    have hcont : ContinuousAt (fun t : ℝ => 1+c*t) 0 := by fun_prop
    simpa only [mul_zero,add_zero] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hf
  have hb : Tendsto (fun t : ℝ => Real.sqrt (1+c*t)) (𝓝[>] 0) (𝓝 1) := by
    simpa only [Function.comp_def,Real.sqrt_one] using hsqrt
  have hlower : Tendsto (fun t => (Real.sqrt (1+c*t)/(1+c*t))*known t) (𝓝[>] 0)
      (𝓝 ‖informedReferencePivotCoefficient A g D R F‖) := by
    simpa only [Pi.div_apply,div_self one_ne_zero,one_mul] using (hb.div hf one_ne_zero).mul hknown
  have hupper : Tendsto (fun t => Real.sqrt (1+c*t)*known t) (𝓝[>] 0)
      (𝓝 ‖informedReferencePivotCoefficient A g D R F‖) := by simpa only [one_mul] using hb.mul hknown
  have hct : ∀ᶠ t : ℝ in 𝓝[>] 0,c*t<1 := by
    have hcont : ContinuousAt (fun t : ℝ => c*t) 0 := by fun_prop
    have h0 : c*0<(1 : ℝ) := by norm_num
    exact (hcont.tendsto.eventually (gt_mem_nhds h0)).filter_mono nhdsWithin_le_nhds
  have hsqueeze : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (Real.sqrt (1+c*t)/(1+c*t))*known t≤ informedSourceRisk directions A g (S t) t ∧
        informedSourceRisk directions A g (S t) t≤Real.sqrt (1+c*t)*known t := by
    filter_upwards [hct,self_mem_nhdsWithin] with t hct ht
    exact informedPhysicalScenario_risk_squeeze_basis directions A hA g hg hc D F c t hc0 ht hct
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
    (hsqueeze.mono fun _ h => h.1) (hsqueeze.mono fun _ h => h.2)

/-- The original S specialization of the common native-basis theorem.
Use: preserve the established step-policy physical source interface.
Article: main_krylov, thm:local(b).
Proof: specialize the shared genuine physical theorem to the S basis. -/
theorem informedPhysicalScenario_own_risk_tendsto
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1)
    (D : ℕ → Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (R F : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hD : ∀ l<n,(D l).IsSymm) (hF : F.IsSymm) (c : ℝ) (hc0 : 0≤c)
    (hR : cgOperator R=c • InnerProductSpace.rankOne ℝ
      (canonicalCGUnitStep A g n) (canonicalCGUnitStep A g n)) :
    Tendsto (fun t : ℝ => informedSourceRisk false A g (informedPhysicalScenario A hA g hg hc D F c t) t)
      (𝓝[>] 0) (𝓝 ‖informedReferencePivotCoefficient A g D R F‖)  := by
  exact informedPhysicalScenario_own_risk_tendsto_basis false A hA g hg hc D R F hD hF c hc0 hR

/-- A genuine original admissible physical source family attains the
complete informed K_X(c) constant for the actual informed S executor,
in the original own-base risk ratio, on every true full reference of
dimension at least two and every nonnegative individual budget profile.
Use: the original source-wide upper coefficient is physically sharp,
including all zero budgets and without a prescribed scalar maximizer.
Article: main_krylov, thm:local(b), full actual physical informed attainment.
Proof: the genuine CG-frame correlated attainer gives real symmetric
matrices and the exact last-axis rank-one prior. The original physical
scenario lift obeys every true own-base admissibility constraint. Its
actual native risk limit equals the attained genuine coefficient norm. -/
theorem knownBase_informed_physical_attainment_basis (directions : Bool)
    (A : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+2))) (hcount : referenceAtomCount A hA g=n+2)
    (omega : ℕ → ℝ) (homega : ∀ l<n+1,0≤omega l)
    (w c : ℝ) (hw : 0≤w) (hc0 : 0≤c) :
    ∃ S : ℝ → Scenario (n+2),
      (∀ t : ℝ,0≤t → (S t).Admissible (n+1) A (c*t) (fun l => omega l*t) (w*t) 0) ∧
        Tendsto (fun t : ℝ => informedSourceRisk directions A g (S t) t) (𝓝[>] 0)
          (𝓝 (informedConstant (∑ l∈range (n+1),omega l) w c)) := by
  have hg : g≠0 := cg_nonstagnation A hA g 0 (by omega)
  have hc : (activeSpectralValues A hA.1 g).card=n+2 := by
    rw [gradientSpectralData_count]
    exact hcount
  obtain ⟨D,R,F,hD,hR,hRn,hRform,hF,hFn,hvalue⟩ := informed_reference_second_order_attained A hA g hcount
    omega (fun l hl => homega l (mem_range.mp hl)) w c hw hc0
  let S := fun t => informedPhysicalScenario A hA g hg hc D F c t
  refine ⟨S,fun t ht => informedPhysicalScenario_admissible A hA g hg hc D F omega
    (fun l hl => hD l (mem_range.mpr hl)) hF w hFn c t hc0 ht,?_⟩
  have h := informedPhysicalScenario_own_risk_tendsto_basis directions A hA g hg hc D R F
    (fun l hl => (hD l (mem_range.mpr hl)).1) hF c hc0 hRform
  exact hvalue ▸ h

/-- The original S specialization of the common native-basis theorem.
Use: preserve the established step-policy physical source interface.
Article: main_krylov, thm:local(b).
Proof: specialize the shared genuine physical theorem to the S basis. -/
theorem knownBase_informed_physical_attainment
    (A : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+2))) (hcount : referenceAtomCount A hA g=n+2)
    (omega : ℕ → ℝ) (homega : ∀ l<n+1,0≤omega l)
    (w c : ℝ) (hw : 0≤w) (hc0 : 0≤c) :
    ∃ S : ℝ → Scenario (n+2),
      (∀ t : ℝ,0≤t → (S t).Admissible (n+1) A (c*t) (fun l => omega l*t) (w*t) 0) ∧
        Tendsto (fun t : ℝ => informedSourceRisk false A g (S t) t) (𝓝[>] 0)
          (𝓝 (informedConstant (∑ l∈range (n+1),omega l) w c))  := by
  exact knownBase_informed_physical_attainment_basis false A hA g hcount omega homega w c hw hc0

end
end krylov.OneGradient
