import krylov.Information.MidpointPolicy
import krylov.Information.ChangedModelExecution
import krylov.Information.KnownBaseLower

/-!
Article: main_krylov, thm:C2(c), actual informed sharp upper bound.
Use: the genuine finite-history midpoint policy obeys the sharp quadratic
coefficient with one common cubic loss before every primitive source scenario.
Source: actual observed-hyperplane reconstruction, derived moving-normal
tube and the genuine joint source/model-change terminal expansion.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant krylov.Envelope
  krylov.Correction krylov.Methods krylov.LinearAlgebra krylov.Stability krylov.Variation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ}

/-- The actual informed midpoint policy has the sharp original one-increment coefficient with a uniform cubic remainder over all genuine finite symmetric source coordinates.
Use: the nonsmooth finite-data midpoint is an actual method, and all constants precede every source scenario and budget.
Article: main_krylov, thm:C2(c), actual all-source informed canonical upper bound.
Proof: the actual query-normal tube identifies the real observed midpoint
and bounds its first-order displacement. Genuine completion geometry bounds
its size and its hidden-diagonal/cross coefficient. Insert that possibly
nonsmooth scalar in the independent model-coordinate cubic tube, identify
the exact native leading vector, and use the true positive terminal CG
step norm to absorb the common absolute cubic loss. -/
theorem source_midpoint_cubic_upper (base : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hcount : referenceAtomCount base hb g=N+1) (hN : 0<N) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ (ω : ℝ), 0≤ω → ω≤δ →
      ∀ (Θ : symmetricScenarios (N+1) (N+1)), ‖Θ‖≤ω →
      ∀ (M : Matrix (Fin (N+1)) (Fin (N+1)) ℝ), M.IsSymm → ‖M‖≤ω →
      matrixSequenceExtension N Θ.val.1=firstIncrement M →
      matrixSequenceExtension (N+1) Θ.val.2 N=0 →
      ‖cgOperator (metricRoot base)⁻¹
        (probedGradient (knownBaseMidpointMethod base g ω) (scenarioProbe base Θ.val) (scenarioCorrection base Θ.val) g (N+1))‖≤
        ‖canonicalCGStep base g N‖*((2/(3*Real.sqrt 3))*ω^2+C*ω^3) := by
  -- Fix the genuine normal and modified-executor tubes before all scenario and midpoint choices.
  obtain ⟨δ₁,L,hδ₁,hL,hnormal⟩ := sourceUnobservedNormal_tube base hb g hcount
  obtain ⟨δ₂,C₀,hδ₂,hC₀,htube⟩ := scenario_modified_cubic_tube base hb g (le_of_eq hcount.symm) hN (midpointModelDirection base g)
  let φ := ‖canonicalCGStep base g N‖
  have hφ : 0<φ := norm_pos_iff.mpr (canonicalCGStep_ne_zero base hb g N (fun i hi => cg_nonstagnation base hb g i (by omega)))
  refine ⟨min δ₁ δ₂,C₀/φ+2*L+1,lt_min hδ₁ hδ₂,by positivity,?_⟩
  intro ω hω hωδ Θ hΘ M hM hMω hE hF
  have hΘδ : ‖Θ‖≤δ₁ := hΘ.trans (hωδ.trans (min_le_left _ _))
  obtain ⟨hu,hv,hdis⟩ := hnormal Θ hΘδ
  let H := methodRun (rfcMethod fullMemory 1) (scenarioProbe base Θ.val) (scenarioCorrection base Θ.val) g N
  let z := probedProbe (rfcMethod fullMemory 1) (scenarioProbe base Θ.val) (scenarioCorrection base Θ.val) g N
  let q := observedMidpoint base g ω H z
  have hq : q=budgetCompletionMidpoint ω (sourceUnobservedNormal base g Θ) (canonicalCGUnitStep base g 0) M :=
    observedMidpoint_run base hb g hcount Θ hu hv M hE ω
  have ho := canonicalCG_frame_of_full_atoms base hb g hcount
  have he : ‖canonicalCGUnitStep base g 0‖=1 := by simpa only [Fin.val_zero] using ho.norm_eq_one (0 : Fin (N+1))
  have hf : ‖canonicalCGUnitStep base g N‖=1 := by simpa only [Fin.val_last] using ho.norm_eq_one (Fin.last N)
  have hef : inner ℝ (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g N)=0 := by
    simpa only [Fin.val_zero,Fin.val_last] using ho.inner_eq_zero (i := 0) (j := Fin.last N)
      (by intro h; have hv' : (0 : ℕ)=N := congrArg Fin.val h; omega)
  have hqω : |q|≤ω := by rw [hq]; exact (budgetCompletionMidpoint_bounds ω hω _ _ hv he M hM hMω).1
  have hcoefficient : |inner ℝ (canonicalCGUnitStep base g 0) (cgOperator M (canonicalCGUnitStep base g 0))-q| *
      |inner ℝ (canonicalCGUnitStep base g 0) (cgOperator M (canonicalCGUnitStep base g N))|≤
        (2/(3*Real.sqrt 3))*ω^2+2*L*ω^3 := by
    have hc := budgetCompletionMidpoint_coefficient_bound ω hω _ _ _ hv he hf hef M hM hMω
    rw [← hq] at hc
    have hdn : ‖sourceUnobservedNormal base g Θ-canonicalCGUnitStep base g 0‖≤L*ω :=
      hdis.trans (mul_le_mul_of_nonneg_left hΘ hL.le)
    calc
      _ ≤ (2/(3*Real.sqrt 3))*ω^2+2*ω^2*‖sourceUnobservedNormal base g Θ-canonicalCGUnitStep base g 0‖ := hc
      _ ≤ (2/(3*Real.sqrt 3))*ω^2+2*ω^2*(L*ω) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hdn (by positivity : 0≤2*ω^2))
      _ = _ := by ring
  -- Selector size, rather than selector regularity, puts the real decision in the actual joint cubic tube.
  have hsize : max ‖Θ‖ |q|≤ω := max_le hΘ hqω
  have ht := htube Θ q (hsize.trans (hωδ.trans (min_le_right _ _)))
  dsimp only at ht
  rw [hE,hF,midpointModelDirection_leading base hb g hcount hN M q] at ht
  let v := φ • (((inner ℝ (canonicalCGUnitStep base g 0) (cgOperator M (canonicalCGUnitStep base g 0))-q)*
    inner ℝ (canonicalCGUnitStep base g 0) (cgOperator M (canonicalCGUnitStep base g N))) • canonicalCGUnitStep base g 0)
  let y := cgOperator (metricRoot base)⁻¹
    (modifiedTerminalGradient (scenarioProbe base Θ.val) (scenarioCorrection base Θ.val) g N (q • midpointModelDirection base g))
  have hvn : ‖v‖≤φ*((2/(3*Real.sqrt 3))*ω^2+2*L*ω^3) := by
    simp only [v,norm_smul,Real.norm_eq_abs,abs_of_nonneg hφ.le,abs_mul,he,mul_one]
    exact mul_le_mul_of_nonneg_left hcoefficient hφ.le
  have hyn : ‖y+v‖≤C₀*ω^3 := ht.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ((norm_nonneg Θ).trans (le_max_left ‖Θ‖ |q|)) hsize 3) hC₀.le)
  change ‖cgOperator (metricRoot base)⁻¹ (probedGradient (changedFinalMethod N (midpointModelChange base g ω)) _ _ g (N+1))‖≤_
  rw [changedFinalMethod_modifiedGradient]
  change ‖y‖≤φ*((2/(3*Real.sqrt 3))*ω^2+(C₀/φ+2*L+1)*ω^3)
  calc
    ‖y‖=‖(y+v)-v‖ := congrArg norm (by abel)
    _ ≤ ‖y+v‖+‖v‖ := norm_sub_le _ _
    _ ≤ C₀*ω^3+φ*((2/(3*Real.sqrt 3))*ω^2+2*L*ω^3) := add_le_add hyn hvn
    _ ≤ _ := by
      have hcancel : φ*(C₀/φ)=C₀ := mul_div_cancel₀ C₀ hφ.ne'
      nlinarith only [mul_nonneg hφ.le (pow_nonneg hω 3),congrArg (fun t : ℝ => t*ω^3) hcancel]



end
end krylov.Information
