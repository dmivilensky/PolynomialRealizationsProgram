import krylov.Information.FirstIncrementScenario
import krylov.Information.RFCFirstIncrement
import krylov.Information.KnownBaseMinimaxBound

/-!
Article: main_krylov, thm:C2(c), ordinary RFC worst known-base risk.
Use: a genuine admissible physical single-increment witness gives the
sharp one-half coefficient for actual RFC, with the matching full-source
upper bound, derived finite supremum and one common cubic loss.
Source: actual planar reflection budgets, genuine joint source cubic tube,
exact physical output reconstruction and the proved all-source RFC upper.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant krylov.Envelope
  krylov.Correction krylov.Methods krylov.LinearAlgebra krylov.Stability krylov.Variation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ}

/-- A true additive residual bound controls the original leading-vector norm by the actual output norm and the same loss.
Use: transfer a genuine vector expansion to a quantitative actual-risk lower bound.
Article: main_krylov, thm:C2(c), reverse norm comparison.
Proof: subtract the true output from the bounded sum and apply the norm triangle inequality. -/
theorem norm_lower_of_add_bound {E : Type*} [SeminormedAddCommGroup E]
    (y v : E) (b : ℝ) (h : ‖y+v‖≤b) : ‖v‖≤b+‖y‖ := by
  calc
    ‖v‖=‖(y+v)-y‖ := congrArg norm (by abel)
    _ ≤ ‖y+v‖+‖y‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add h (le_refl ‖y‖)

/-- The actual original known-base source supremum of ordinary RFC has leading coefficient at least one half, with one common cubic loss.
Use: the concrete actual source witness proves sharpness of ordinary RFC, beyond a geometric formal coefficient.
Article: main_krylov, thm:C2(c), genuine ordinary RFC worst-source lower bound.
Proof: scale the true first/last CG planar reflection by the original
budget and realize it as an actual admissible physical source. The common
finite-source cubic expansion has the exact attained one-half leading
vector. Actual physical output reconstruction and the reverse norm
comparison give its genuine normalized risk in the true source supremum. -/
theorem knownBase_rfc_lower (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N) (hcount : referenceAtomCount A hA g=N+1) :
    ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ ω : ℝ, 0≤ω → ω≤δ →
      ENNReal.ofReal (ω^2/2-C*ω^3)≤knownBaseWorstOutputRatio (rfcMethod fullMemory 1) A g N ω := by
  -- Choose the genuine joint executor remainder tube before every physical source witness.
  obtain ⟨δ,C₀,hδ,hC₀,htube⟩ := scenario_cubic_tube A hA g (le_of_eq hcount.symm) hN
  let φ := ‖canonicalCGStep A g N‖
  have hφ : 0<φ := norm_pos_iff.mpr (canonicalCGStep_ne_zero A hA g N
    (fun i hi => cg_nonstagnation A hA g i (by omega)))
  refine ⟨δ/2,C₀/φ,half_pos hδ,by positivity,?_⟩
  intro ω hω hωδ
  obtain ⟨hM,hMn,hvalue⟩ := rfcSingleIncrementWitness_spec A hA g hN hcount
  let M := ω • rfcSingleIncrementWitness A g
  have hMnω : ‖M‖≤ω := by
    rw [norm_smul,Real.norm_of_nonneg hω]
    exact (mul_le_mul_of_nonneg_left hMn hω).trans_eq (mul_one _)
  let S := firstIncrementScenario A M
  have hS : S.Admissible N A 0 (firstBudget ω) 0 0 := firstIncrementScenario_admissible A M hA (hM.smul _) ω hMnω N
  let Θ := S.symmetricParameters N (fun i hi => (hS.2.2.1 i hi).1) hS.2.2.2.1
    (fun i hi => (hS.2.2.2.2.2 i hi).1)
  have hΘ : ‖Θ‖≤ω := S.symmetricParameters_norm_le N A 0 (firstBudget ω) 0 0 hS hω
    (fun i _ => by
      by_cases hi : i=0
      · simp only [firstBudget,ite_eq_left hi,le_refl]
      · simpa only [firstBudget,ite_eq_right hi] using hω) hω hω
  have ht := htube Θ (hΘ.trans_lt (hωδ.trans_lt (half_lt_self hδ)))
  obtain ⟨hE,hF⟩ := firstIncrementScenario_parameters A M hA hN
  change matrixSequenceExtension N Θ.val.1=firstIncrement M at hE
  change matrixSequenceExtension (N+1) Θ.val.2 N=0 at hF
  rw [hE,hF,hvalue ω] at ht
  -- Reconstruct the true physical returned gradient before estimating its actual normalized risk.
  have hout := S.canonicalParameters_output N hS.1 (rfcMethod fullMemory 1) g
  change probedGradient (rfcMethod fullMemory 1) (scenarioProbe A (S.canonicalParameters N))
    (scenarioCorrection A (S.canonicalParameters N)) g (N+1)=_ at hout
  have hcoord : Θ.val=S.canonicalParameters N := rfl
  rw [hcoord,hout] at ht
  let y := cgOperator (metricRoot A)⁻¹ (probedGradient (rfcMethod fullMemory 1) S.probeOracle (S.correctionOracle N) g (N+1))
  let v := φ • ((ω^2/2) • canonicalCGUnitStep A g 0)
  have htω : ‖y+v‖≤C₀*ω^3 := ht.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hΘ 3) hC₀.le)
  have he : ‖canonicalCGUnitStep A g 0‖=1 := by
    simpa only [Fin.val_zero] using (canonicalCG_frame_of_full_atoms A hA g hcount).norm_eq_one (0 : Fin (N+1))
  have hv : ‖v‖=φ*(ω^2/2) := by
    simp only [v,norm_smul,Real.norm_eq_abs,abs_of_nonneg hφ.le,abs_of_nonneg (by positivity : 0≤ω^2/2),he,mul_one]
  have hy : φ*(ω^2/2)≤C₀*ω^3+‖y‖ := hv.symm.trans_le (norm_lower_of_add_bound y v (C₀*ω^3) htω)
  have hlower : ω^2/2-(C₀/φ)*ω^3≤S.outputRatio (rfcMethod fullMemory 1) g N := by
    change _≤‖y‖/‖cgCanonicalError A g N‖
    rw [terminal_step_error_norm A hA g (le_of_eq hcount.symm)]
    apply (le_div_iff₀ hφ).mpr
    have hc : (C₀/φ)*φ=C₀ := div_mul_cancel₀ C₀ hφ.ne'
    nlinarith only [hy,congrArg (fun t : ℝ => t*ω^3) hc]
  apply (ENNReal.ofReal_le_ofReal hlower).trans
  unfold knownBaseWorstOutputRatio
  exact le_iSup_of_le (⟨S,hS,rfl⟩ : {T : Scenario (N+1) //
    T.Admissible N A 0 (firstBudget ω) 0 0 ∧ T.base=A}) le_rfl



end
end krylov.Information
