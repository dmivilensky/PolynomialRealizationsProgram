import krylov.Envelope.CanonicalSingletonPath
import krylov.Methods.OrthogonalProbe
import krylov.Methods.CorrectionFreeOracles
import krylov.Methods.FiniteOracleCharts

set_option autoImplicit false
/-!
Article: main_krylov, s3:thm:cf, actual exact newest-increment correction-free response.
Use: force the real final output of every genuine correction-free globally
CG-consistent policy by a true newest source increment without changing any
actual earlier observation or real final search curvature.
Source: genuine source singleton segment identities, actual prefix nonanticipation,
true global quadratic direction scaling and exact orthogonal-probe search algebra.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Stability krylov.Variation Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- Every actual correction-free globally CG-consistent method has the exact genuine affine final-gradient response to a true newest increment orthogonal to its real last CG direction.
Use: Every actual correction-free globally CG-consistent method has the exact genuine affine final-gradient response to a true newest increment orthogonal to its real last CG direction.
Article: main_krylov, s3:thm:cf, actual exact newest-increment correction-free response.
Proof: All genuine earlier source segments remain exactly the actual quadratic reference, so the real complete prefix and chosen direction are fixed. True positive CG direction scaling cancels in the genuine search. The actual orthogonal probe perturbation preserves real curvature exactly, yielding the stated true affine output for every parameter. -/
theorem correctionFree_last_singleton_gradient
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m) (hfree : Methods.CorrectionFree m)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (k : ℕ) (D : Matrix (Fin n) (Fin n) ℝ)
    (horth : inner ℝ (CG.direction (cgOperator base) g (k+1))
      (cgOperator (metricRoot base*D*metricRoot base) (CG.direction (cgOperator base) g (k+1)))=0) (t : ℝ) :
    probedGradient m (canonicalFCPath base (Pi.single k D) t) (canonicalFCPath base (Pi.single k D) t) g (k+2)=
      CG.gradient (cgOperator base) g (k+2)+
        t • cgOperator (metricRoot base*D*metricRoot base) (referenceStep (cgOperator base) g (k+1)) := by
  -- The genuine newest increment leaves every actual earlier oracle answer and full observed history exactly quadratic.
  let Q := cgOperator base
  let T := cgOperator (metricRoot base*D*metricRoot base)
  let A := canonicalFCPath base (Pi.single k D)
  let H := methodRun m (fun _ => Q) (fun _ => Q) g (k+1)
  have hQ := cgOperator_positive base hb
  have hH : methodRun m (A t) (A t) g (k+1)=H :=
    methodRun_congr_prefix m _ _ _ _ g (k+1)
      (fun j hj => singleton_canonicalPath_before base k j D (by omega) t)
      (fun j hj => singleton_canonicalPath_before base k j D (by omega) t)
  have hg : H.gradient=CG.gradient Q g (k+1) := quadratic_gradient_eq_cg m hm Q hQ.1 hQ.2 g (k+1)
  obtain ⟨c,hc,hd,_⟩ := hm Q hQ.1 hQ.2 g (k+1)
  have hdH : m.direction H=c • CG.direction Q g (k+1) := hd
  -- Preserve the true arbitrary positive CG direction scale through the actual final probe and exact-search quotient.
  have hz : A t (k+1) (c • CG.direction Q g (k+1))=
      c • (Q (CG.direction Q g (k+1))+t • T (CG.direction Q g (k+1))) := by
    dsimp only [A]
    rw [singleton_canonicalPath_last]
    simp only [_root_.add_apply,_root_.smul_apply,map_smul]
    module
  rw [correctionFree_gradient_succ m hfree (A t) (A t) g (k+1)]
  change searchedGradient (methodRun m (A t) (A t) g (k+1)).gradient
    (m.direction (methodRun m (A t) (A t) g (k+1)))
    (A t (k+1) (m.direction (methodRun m (A t) (A t) g (k+1))))=_
  rw [hH,hg,hdH,hz,searchedGradient_smul _ _ _ hc.ne',
    searchedGradient_orthogonal_probe _ _ _ _ horth t]
  change CG.gradient Q g ((k+1)+1)+t • (CG.length Q g (k+1) • T (CG.direction Q g (k+1)))=_
  simp only [referenceStep,map_smul,Q,T,Nat.add_assoc]
end
end krylov.Envelope
