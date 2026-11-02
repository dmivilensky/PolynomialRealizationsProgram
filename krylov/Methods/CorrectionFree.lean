import krylov.Variation.CorrectionFree
import krylov.Methods.ExecutedProbed
import krylov.Reference.EnergyMinimum
import krylov.Variation.ReferenceFlags

/-!
Article: main_krylov, s3:cor:cf, exact genuine correction-free obstruction.
Use: instantiate the proved terminal data fibre for every actual globally
CG-consistent correction-free policy and obtain its exact true terminal
residual and genuinely positive physical adversarial query operators.
Source: the actual complete-history indistinguishability theorem, true CG
terminal energy tail and real planar positive-definiteness criterion.
-/

namespace krylov.Methods
noncomputable section
open Matrix Finset krylov.Reference krylov.Secant krylov.LinearAlgebra krylov.Variation
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual probed policy makes no correction query on any observed history.
Use: The actual probed policy makes no correction query on any observed history.
Article: main_krylov, s3:cor:cf.
Proof: Reuse the existing correction-free predicate on the genuine decision tree. -/
def CorrectionFree {E : Type*} (m : ProbedMethod E) : Prop := krylov.Variation.CorrectionFree m

/-- Every actual CG-consistent correction-free policy has the printed exact terminal residual on the genuine common planar perturbations.
Use: Every actual CG-consistent correction-free policy has the printed exact terminal residual on the genuine common planar perturbations.
Article: main_krylov, s3:cor:cf.
Proof: The actual terminal data fibre determines the post-search gradient. Its genuine correction-free decision tree leaves that gradient unchanged; true terminal CG energy identifies the real norm. -/
theorem correctionFree_terminal_exact (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hn : 0<n) (hcount : referenceAtomCount base hb g=n+1)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (n+1)))) (hm : CGConsistent m) (hfree : CorrectionFree m)
    (ω : ℕ → ℝ) (hω : ∀ l∈range n, 0≤ω l) :
    let e := canonicalCGUnitStep base g 0
    let h := canonicalCGUnitStep base g n
    let A := fun k => Matrix.toEuclideanCLM (𝕜 := ℝ) (physicalTerminalSegments base e h ω (fun _ => 0) (fun _ => 0) n k)
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (probedGradient m A A g (n+1))‖=
      (∑ l∈range n, ω l)*‖cgCanonicalError base g n‖ := by
  -- Reuse the exact actual obstruction; only its genuine terminal-energy normalization changes.
  have hres := krylov.Variation.correctionFree_terminal_residual base hb g hn hcount m hm hfree ω
    (fun l hl => hω l (mem_range.mpr hl))
    (fun k => Matrix.toEuclideanCLM (𝕜 := ℝ) (physicalTerminalSegments base
      (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g n) ω 0 0 n k))
  have hlast : Real.sqrt (cgEnergy base g n)=‖cgCanonicalError base g n‖ := by
    have he := cgEnergy_tail base hb g (l := n) (by rw [hcount];omega)
    simp only [hcount,Nat.Ico_succ_singleton,sum_singleton] at he
    rw [← he,Real.sqrt_sq (norm_nonneg _)]
  simpa only [probedGradient,hlast,Pi.zero_def] using hres

/-- All genuine physical operators in the correction-free adversarial cycle are positive definite below total budget one.
Use: All genuine physical operators in the correction-free adversarial cycle are positive definite below total budget one.
Article: main_krylov, s3:cor:cf.
Proof: Every actual cross prefix is bounded by the true total budget. Genuine CG orthogonality gives the real positive canonical plane; invertible actual root congruence transfers positivity to the physical operator. -/
theorem correctionFree_terminal_positive (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hn : 0<n) (hcount : referenceAtomCount base hb g=n+1)
    (ω : ℕ → ℝ) (hω : ∀ l∈range n, 0≤ω l) (hsmall : ∑ l∈range n, ω l<1) :
    ∀ k≤n, (physicalTerminalSegments base (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g n)
      ω (fun _ => 0) (fun _ => 0) n k).PosDef := by
  intro k hk
  exact krylov.Variation.correctionFree_segments_posDef base hb g hn hcount ω
    (fun l hl => hω l (mem_range.mpr hl)) hsmall hk
end
end krylov.Methods
