import krylov.Stability.FCWorstAsymptotics
import krylov.Variation.CorrectionFree
import krylov.Methods.Classes
import krylov.Methods.ReferenceProbedSteps

set_option autoImplicit false

/-!
Article: main_krylov, s3:cor:cf, exact actual correction-free first variation.
Use: derive the genuine common correction-free path derivative directly
from its complete actual terminal data fibre, without assuming any derivative
formula or smoothness of the raw policy away from that true path.
Source: the actual terminal fibre and no-correction execution, true canonical
physical congruence and the genuine derivative of the resulting real linear path.
-/

namespace krylov.Variation
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.LinearAlgebra krylov.Stability
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual correction-free terminal canonical gradient is exactly the genuine common planar residual vector for every real cross coefficient.
Use: The actual correction-free terminal canonical gradient is exactly the genuine common planar residual vector for every real cross coefficient.
Article: main_krylov, s3:cor:cf, exact actual correction-free first variation.
Proof: The real terminal data fibre fixes the actual post-search vector; the true empty correction decision returns it unchanged. -/
theorem correctionFree_terminal_vector
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hn : 0<n) (hcount : referenceAtomCount base hb g=n+1)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (n+1)))) (hm : CGConsistent m) (hfree : CorrectionFree m)
    (x : ℕ → ℝ) (B : ℕ → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))) :
    let A := fun k => Matrix.toEuclideanCLM (𝕜 := ℝ)
      (physicalTerminalSegments base (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g n) x 0 0 n k)
    Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (probedGradient m A B g (n+1))=
      ((∑ l∈range n, x l)*Real.sqrt (cgEnergy base g n)) • canonicalCGUnitStep base g 0 := by
  -- The actual empty correction tree returns the real common post-search vector exactly.
  obtain ⟨_,_,hf⟩ := terminal_data_fibre base hb g hn hcount m hm x
  have he := (hf 0 0 B).2.2.2
  dsimp only at he ⊢
  change Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    (runCorrections (m.correction _ _) _ _).gradient=_
  rw [hfree]
  exact he

/-- The actual symmetric first/last CG-plane increment family for a genuine physical reference.
Use: The actual symmetric first/last CG-plane increment family for a genuine physical reference.
Article: main_krylov, s3:cor:cf, exact actual correction-free first variation.
Proof: Its real coefficients carry the prescribed independent component budgets. -/
def crossIncrements (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (n+1))) (ω : ℕ → ℝ) (l : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  planarMatrix (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g n) 0 (ω l) 0

/-- The actual affine canonical cross-increment FC path is exactly the genuine physical planar terminal fibre.
Use: The actual affine canonical cross-increment FC path is exactly the genuine physical planar terminal fibre.
Article: main_krylov, s3:cor:cf, exact actual correction-free first variation.
Proof: Sum the real planar coefficients, use the true positive-root square identity and identify the actual physical matrix/operator map. -/
theorem crossIncrements_path (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (ω : ℕ → ℝ) (t : ℝ) :
    canonicalFCPath base (crossIncrements base g ω) t=fun k => Matrix.toEuclideanCLM (𝕜 := ℝ)
      (physicalTerminalSegments base (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g n)
        (fun l => t*ω l) 0 0 n k) := by
  -- Compare genuine physical matrices before applying the actual Euclidean operator map.
  funext k
  let R := metricRoot base
  have hp : t • (∑ l∈range k, crossIncrements base g ω l)=
      planarMatrix (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g n) 0 (∑ l∈range k, t*ω l) 0 := by
    simp only [crossIncrements,planarMatrix,zero_smul,zero_add,add_zero]
    rw [← Finset.sum_smul,smul_smul,Finset.mul_sum]
  have heq : base+t • (R*(∑ l∈range k, crossIncrements base g ω l)*R)=
      physicalTerminalSegments base (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g n) (fun l => t*ω l) 0 0 n k := by
    unfold physicalTerminalSegments terminalSegments
    simp only [Pi.zero_apply,sum_const_zero,sub_zero]
    rw [← hp,Matrix.mul_add,Matrix.add_mul,Matrix.mul_one,metricRoot_square base hb,Matrix.mul_smul,Matrix.smul_mul]
  rw [canonicalFCPath,cgOperator,cumulativeDrift,← map_smul,← map_add]
  exact congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ)) heq

/-- Every actual CG-consistent correction-free raw method has the genuine nonzero common first-order planar obstruction along the real prescribed cross path.
Use: Every actual CG-consistent correction-free raw method has the genuine nonzero common first-order planar obstruction along the real prescribed cross path.
Article: main_krylov, s3:cor:cf, exact actual correction-free first variation.
Proof: Exact full-history indistinguishability gives the actual path as a real scalar multiple of its true fixed terminal residual vector. Differentiate that genuine executed linear path; no presumed adaptive first variation is used. -/
theorem correctionFree_cross_derivative
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hn : 0<n) (hcount : referenceAtomCount base hb g=n+1)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (n+1)))) (hm : CGConsistent m) (hfree : CorrectionFree m)
    (ω : ℕ → ℝ) :
    HasDerivAt (fun t => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      (probedGradient m (canonicalFCPath base (crossIncrements base g ω) t)
        (canonicalFCPath base (crossIncrements base g ω) t) g (n+1)))
      (((∑ l∈range n, ω l)*Real.sqrt (cgEnergy base g n)) • canonicalCGUnitStep base g 0) 0 := by
  -- Identify the complete actual path before asserting or differentiating its true first variation.
  let v := ((∑ l∈range n, ω l)*Real.sqrt (cgEnergy base g n)) • canonicalCGUnitStep base g 0
  have heq : (fun t => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
      (probedGradient m (canonicalFCPath base (crossIncrements base g ω) t)
        (canonicalFCPath base (crossIncrements base g ω) t) g (n+1)))=fun t : ℝ => t • v := by
    funext t
    rw [crossIncrements_path base hb g ω t]
    rw [correctionFree_terminal_vector base hb g hn hcount m hm hfree]
    rw [← Finset.mul_sum,smul_smul]
    congr 1
    ring
  rw [heq]
  convert! (hasDerivAt_id (0 : ℝ)).smul_const v using 1
  simp only [one_smul,v]
end
end krylov.Variation
