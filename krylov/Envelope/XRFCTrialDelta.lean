import krylov.Envelope.XRFCCanonicalTrialFormulas
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1 and eq:virtual-trial-delta, genuine trial injection decomposition and exact trials.
Use: identify actual virtual injections as original CG injections plus true consecutive trial-delta differences, with the printed canonical formula and vanishing trial terms under genuine exact reference trials.
Source: exact actual accumulated injection difference, proved canonical physical summation by parts and genuine measured trial ratios.
-/

namespace krylov.Envelope
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Variation
open scoped BigOperators
variable {n : ℕ}

/-- The genuine canonical difference of actual effective-gradient and original CG accumulated injection first variations.
Use: The genuine canonical difference of actual effective-gradient and original CG accumulated injection first variations.
Article: main_krylov, thm:E1 and eq:virtual-trial-delta, genuine trial injection decomposition and exact trials.
Proof: Apply the true inverse metric root to the actual differentiated injection difference. -/
def xrfcTrialDelta (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    (xrfcInjectionJet trial (canonicalFCPath base E) (cgOperator base) g k-
      ∑ i∈Finset.range k,cumulativeDrift base E i (referenceStep (cgOperator base) g i))

/-- Every genuine actual virtual injection equals its original CG injection plus the true consecutive canonical trial-delta difference.
Use: Every genuine actual virtual injection equals its original CG injection plus the true consecutive canonical trial-delta difference.
Article: main_krylov, thm:E1 and eq:virtual-trial-delta, genuine trial injection decomposition and exact trials.
Proof: Telescope the actual original cumulative CG injection sum and distribute the genuine inverse-root linear action. -/
theorem xrfc_virtual_injection_decomposition (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      (injectionDifference (xrfcInjectionJet trial (canonicalFCPath base E) (cgOperator base) g) (k+1))=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      (referenceInjection (cgOperator base) g (canonicalFCPath base E) (k+1))+
      xrfcTrialDelta trial base g E (k+1)-xrfcTrialDelta trial base g E k := by
  rw [injectionDifference,referenceInjection,(canonicalFCPath_calculus base E k).2.deriv]
  unfold xrfcTrialDelta
  rw [Finset.sum_range_succ]
  simp only [map_sub,map_add]
  abel

/-- The genuine actual accumulated virtual trial difference has exactly the original printed canonical trial-error and later-correction product formula.
Use: The genuine actual accumulated virtual trial difference has exactly the original printed canonical trial-error and later-correction product formula.
Article: main_krylov, thm:E1 and eq:virtual-trial-delta, genuine trial injection decomposition and exact trials.
Proof: Apply the proved actual canonical virtual trial-delta formula on the real primitive source path. -/
theorem xrfcTrialDelta_printed (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ) (hcount : N≤referenceAtomCount base hb g)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (hT : ∀ k<N,ContDiffAt ℝ 2 (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g k)) :
    let m := xrfcMethod fullMemory trial
    let tau := fun j => trial (oneGradientRun m (fun _ => cgOperator base) g j)
    let rho := fun j => CG.length (cgOperator base) g j-tau j
    xrfcTrialDelta trial base g E N=
      ∑ l∈Finset.range (N-1),((rho l/CG.length (cgOperator base) g l)*Real.sqrt (cgEnergy base g l)*
        (1-trialTailFactor tau rho N l)) • cgOperator (E l) (canonicalCGUnitStep base g l) :=
  xrfc_canonical_trial_delta trial base hb g E N hcount ht hT

/-- Every genuine exact reference trial removes its original actual output trial coefficient.
Use: Every genuine exact reference trial removes its original actual output trial coefficient.
Article: main_krylov, thm:E1 and eq:virtual-trial-delta, genuine trial injection decomposition and exact trials.
Proof: The true missed-line numerator vanishes in the real measured coefficient formula. -/
theorem xrfcTrialCoefficient_exact (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N l : ℕ)
    (he : trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g l)=CG.length (cgOperator base) g l) :
    xrfcTrialCoefficient trial base g N l=0 := by
  dsimp only [xrfcTrialCoefficient]
  rw [he,sub_self,zero_div,mul_zero,zero_mul]

/-- Genuine exact reference trials remove the actual canonical virtual trial-delta correction throughout the original finite prefix.
Use: Genuine exact reference trials remove the actual canonical virtual trial-delta correction throughout the original finite prefix.
Article: main_krylov, thm:E1 and eq:virtual-trial-delta, genuine trial injection decomposition and exact trials.
Proof: Use the proved printed actual trial-delta formula; each true missed-line numerator vanishes at its original used chronological index. -/
theorem xrfcTrialDelta_exact (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (N : ℕ) (hcount : N≤referenceAtomCount base hb g)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (hT : ∀ k<N,ContDiffAt ℝ 2 (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g k))
    (he : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)=CG.length (cgOperator base) g i) :
    xrfcTrialDelta trial base g E N=0 := by
  rw [xrfcTrialDelta_printed trial base hb g E N hcount ht hT]
  dsimp only
  apply Finset.sum_eq_zero
  intro l hl
  rw [he l (by have := Finset.mem_range.mp hl;omega),sub_self,zero_div,zero_mul,zero_mul,zero_smul]
end
end krylov.Envelope
