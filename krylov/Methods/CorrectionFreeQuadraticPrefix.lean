import krylov.Methods.OrthogonalProbe
import krylov.Methods.CorrectionFreeOracles
import krylov.Methods.QuadraticConsistency

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(d), actual final search after matching quadratic probes.
Use: identify the exact real correction-free last-gradient response when earlier oracle actions agree with a genuine quadratic reference.
Source: proved full-history quadratic shadow equality, positive direction-scale invariance and exact orthogonal-probe line-search algebra.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Matching all earlier quadratic probe actions gives an exact affine final response to an orthogonal final probe defect.
Use: Matching all earlier quadratic probe actions gives an exact affine final response to an orthogonal final probe defect.
Article: main_krylov, apB:lem:mu(d), actual final search after matching quadratic probes.
Proof: Identify the actual complete prefix with its true quadratic history, cancel the permitted positive direction scale and use the exact final-search identity. -/
theorem correctionFree_gradient_quadratic_prefix (m : ProbedMethod E)
    (hm : CGConsistent m) (hfree : CorrectionFree m) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (k : ℕ) (A B : ℕ → E →L[ℝ] E)
    (hprobe : ∀ j<k,A j (CG.direction Q g j)=Q (CG.direction Q g j))
    (z : E) (hz : A k (CG.direction Q g k)=Q (CG.direction Q g k)+z)
    (horth : inner ℝ (CG.direction Q g k) z=0) :
    probedGradient m A B g (k+1)=CG.gradient Q g (k+1)+CG.length Q g k • z := by
  -- Matching actual probe actions fixes the whole previous observed history, including every genuine policy decision.
  let H := methodRun m (fun _ => Q) (fun _ => Q) g k
  have hH : methodRun m A B g k=H := cgConsistent_shadow m hm Q hQ hpos A B g k hprobe k le_rfl
  have hg : H.gradient=CG.gradient Q g k := quadratic_gradient_eq_cg m hm Q hQ hpos g k
  obtain ⟨c,hc,hd,_⟩ := hm Q hQ hpos g k
  have hdH : m.direction H=c • CG.direction Q g k := hd
  rw [correctionFree_gradient_succ m hfree A B g k]
  change searchedGradient (methodRun m A B g k).gradient
    (m.direction (methodRun m A B g k)) (A k (m.direction (methodRun m A B g k)))=_
  rw [hH,hg,hdH,map_smul,hz,searchedGradient_smul _ _ _ hc.ne']
  -- The final curvature is unchanged, so the actual line search has an exact affine response.
  have he := searchedGradient_orthogonal_probe (CG.gradient Q g k) (CG.direction Q g k)
    (Q (CG.direction Q g k)) z horth 1
  change searchedGradient (CG.gradient Q g k) (CG.direction Q g k)
    (Q (CG.direction Q g k)+z)=
      CG.gradient Q g (k+1)+CG.length Q g k • z
  simpa only [one_smul,CG.gradient,CG.direction,CG.length,cgRun,cgAdvance] using he
end
end krylov.Methods
