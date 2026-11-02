import krylov.Methods.QuadraticConsistency
import krylov.Reference.Stopping
import krylov.Methods.InformationSpan

/-!
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG consistency bridges.
Use: construct genuinely data-only Hestenes--Stiefel and Hager--Zhang policies,
prove their actual globally quadratic CG transcripts and their actual
information-class direction and correction-span restrictions.
Source: HestenesStiefel52, HagerZhang05; exact-search orthogonality and the
already proved actual CG geometric invariants, including true stopping.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine observed Hestenes--Stiefel coefficient.
Use: The genuine observed Hestenes--Stiefel coefficient.
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG consistency bridges.
Proof: It uses only the current and previous observed gradients and the actual preceding direction. -/
def hsCoefficient (gnew gold d : E) : ℝ := inner ℝ gnew (gnew-gold)/inner ℝ d (gnew-gold)

/-- The genuine observed Hager--Zhang coefficient.
Use: The genuine observed Hager--Zhang coefficient.
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG consistency bridges.
Proof: Its real numerator includes the standard observed secant projection term. -/
def hzCoefficient (gnew gold d : E) : ℝ :=
  let y := gnew-gold
  inner ℝ (y-(2*‖y‖^2/inner ℝ d y) • d) gnew/inner ℝ d y

/-- The actual Hestenes--Stiefel and Hager--Zhang coefficients coincide with the measured quadratic CG coefficient at every actual reference index, including stopping.
Use: The actual Hestenes--Stiefel and Hager--Zhang coefficients coincide with the measured quadratic CG coefficient at every actual reference index, including stopping.
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG consistency bridges.
Proof: True next-gradient orthogonality identifies both real numerators and the actual denominator. If the true next gradient is zero, both actual coefficients are exactly zero. -/
theorem nonlinear_cg_coefficients (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) :
    hsCoefficient (CG.gradient Q g (k+1)) (CG.gradient Q g k) (CG.direction Q g k)=CG.beta Q g k ∧
    hzCoefficient (CG.gradient Q g (k+1)) (CG.gradient Q g k) (CG.direction Q g k)=CG.beta Q g k := by
  -- Treat the actual solved step first, so no spurious positive denominator is required after termination.
  by_cases hn : CG.gradient Q g (k+1)=0
  · simp [hsCoefficient,hzCoefficient,hn,CG.beta]
  have hpre : ∀ i < k+1, CG.gradient Q g i≠0 := by
    intro i hi hz
    exact hn (CG.gradient_eq_zero_of_le Q g hz (by omega))
  have hk := CG.invariant Q hQ hpos g k (fun i hi => hpre i (by omega))
  have hnext := CG.invariant Q hQ hpos g (k+1) hpre
  have hgg : inner ℝ (CG.gradient Q g (k+1)) (CG.gradient Q g k)=0 := by
    rw [real_inner_comm]
    exact hnext.old_gradient k (Nat.lt_succ_self k)
  have hdg : inner ℝ (CG.direction Q g k) (CG.gradient Q g (k+1))=0 :=
    hnext.old_direction k (Nat.lt_succ_self k)
  have hden : inner ℝ (CG.direction Q g k) (CG.gradient Q g (k+1)-CG.gradient Q g k)=‖CG.gradient Q g k‖^2 := by
    rw [inner_sub_right,hdg,hk.search_pair,zero_sub,neg_neg]
  constructor
  · simp only [hsCoefficient,hden,inner_sub_right,real_inner_self_eq_norm_sq,hgg,sub_zero]
  · simp only [hzCoefficient,hden,inner_sub_left,real_inner_smul_left,hdg,mul_zero,sub_zero,
      real_inner_self_eq_norm_sq,hnext.old_gradient k (Nat.lt_succ_self k),sub_zero]

/-- The actual correction-free nonlinear CG policy with its observed scalar recurrence rule.
Use: The actual correction-free nonlinear CG policy with its observed scalar recurrence rule.
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG consistency bridges.
Proof: The actual newest record and preceding observed gradient determine the next direction; no unknown operator is supplied. -/
def nonlinearCGMethod (coefficient : E → E → E → ℝ) : ProbedMethod E where
  direction H := match H.records with
    | [] => -H.initial
    | r::rs => -r.gradient+coefficient r.gradient (History.mk H.initial rs).gradient r.direction • r.direction
  correction _ _ := .done

/-- Any actual observed coefficient rule agreeing with true CG coefficients has exactly the genuine quadratic CG gradients and directions.
Use: Any actual observed coefficient rule agreeing with true CG coefficients has exactly the genuine quadratic CG gradients and directions.
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG consistency bridges.
Proof: Induct through the actual full history and real exact search, then use the proved scalar coefficient identity. -/
theorem nonlinearCGMethod_static (coefficient : E → E → E → ℝ) (Q : E →L[ℝ] E)
    (g : E) (hcoef : ∀ k, coefficient (CG.gradient Q g (k+1)) (CG.gradient Q g k)
      (CG.direction Q g k)=CG.beta Q g k) (k : ℕ) :
    let H := methodRun (nonlinearCGMethod coefficient) (fun _ => Q) (fun _ => Q) g k
    H.gradient=CG.gradient Q g k ∧ (nonlinearCGMethod coefficient).direction H=CG.direction Q g k := by
  -- Preserve the true complete history while comparing both actual next state components.
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    let H := methodRun (nonlinearCGMethod coefficient) (fun _ => Q) (fun _ => Q) g k
    have hg : H.gradient=CG.gradient Q g k := ih.1
    have hd : (nonlinearCGMethod coefficient).direction H=CG.direction Q g k := ih.2
    constructor
    · change searchedGradient H.gradient ((nonlinearCGMethod coefficient).direction H)
        (Q ((nonlinearCGMethod coefficient).direction H))=_
      rw [hg,hd]
      rfl
    · change -searchedGradient H.gradient ((nonlinearCGMethod coefficient).direction H)
        (Q ((nonlinearCGMethod coefficient).direction H))+
        coefficient (searchedGradient H.gradient ((nonlinearCGMethod coefficient).direction H)
          (Q ((nonlinearCGMethod coefficient).direction H))) H.gradient
          ((nonlinearCGMethod coefficient).direction H) • ((nonlinearCGMethod coefficient).direction H)=_
      rw [hg,hd]
      change -CG.gradient Q g (k+1)+coefficient (CG.gradient Q g (k+1)) (CG.gradient Q g k)
        (CG.direction Q g k) • CG.direction Q g k=_
      rw [hcoef]
      rfl

/-- A genuine quadratic coefficient identity proves global CG consistency of the actual nonlinear CG policy.
Use: A genuine quadratic coefficient identity proves global CG consistency of the actual nonlinear CG policy.
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG consistency bridges.
Proof: The actual static transcript has scale one and the true correction tree is empty. -/
theorem nonlinearCGMethod_consistent (coefficient : E → E → E → ℝ)
    (hcoef : ∀ (Q : E →L[ℝ] E), Q.toLinearMap.IsSymmetric →
      (∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) → ∀ g k,
      coefficient (CG.gradient Q g (k+1)) (CG.gradient Q g k) (CG.direction Q g k)=CG.beta Q g k) :
    CGConsistent (nonlinearCGMethod coefficient) := by
  intro Q hQ hpos g k
  refine ⟨1,zero_lt_one,?_,trivial⟩
  simpa only [one_smul] using (nonlinearCGMethod_static coefficient Q g (hcoef Q hQ hpos g) k).2

/-- The genuine executed Hestenes--Stiefel policy is globally CG-consistent.
Use: The genuine executed Hestenes--Stiefel policy is globally CG-consistent.
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG consistency bridges.
Proof: Use the actual coefficient identity and full-history execution bridge. -/
theorem hsMethod_consistent : CGConsistent (nonlinearCGMethod (hsCoefficient : E → E → E → ℝ)) :=
  nonlinearCGMethod_consistent hsCoefficient (fun Q hQ hpos g k => (nonlinear_cg_coefficients Q hQ hpos g k).1)

/-- The genuine executed Hager--Zhang policy is globally CG-consistent.
Use: The genuine executed Hager--Zhang policy is globally CG-consistent.
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG consistency bridges.
Proof: Use its true coefficient identity and the same actual execution bridge. -/
theorem hzMethod_consistent : CGConsistent (nonlinearCGMethod (hzCoefficient : E → E → E → ℝ)) :=
  nonlinearCGMethod_consistent hzCoefficient (fun Q hQ hpos g k => (nonlinear_cg_coefficients Q hQ hpos g k).2)

/-- Every actual observed nonlinear CG scalar recurrence respects the genuine source probed information class on arbitrary histories.
Use: Every actual observed nonlinear CG scalar recurrence respects the genuine source probed information class on arbitrary histories.
Article: main_krylov, cor:lm and s3:cor:qn, actual nonlinear CG consistency bridges.
Proof: The true current gradient and newest recorded direction are observed; the actual correction tree is empty. -/
theorem nonlinearCGMethod_spanRestricted (coefficient : E → E → E → ℝ) (memory : ℕ → ℕ) :
    ProbedSpanRestricted memory (nonlinearCGMethod coefficient) := by
  -- Information admissibility is proved on every actual input history, independently of quadratic consistency.
  intro H
  constructor
  · cases hrec : H.records with
    | nil =>
      simp only [nonlinearCGMethod,hrec]
      have hg := H.gradient_mem_observedSpan
      simpa only [History.gradient,hrec] using H.observedSpan.neg_mem hg
    | cons r rs =>
      simp only [nonlinearCGMethod,hrec]
      have hg : r.gradient∈H.observedSpan := by simpa only [History.gradient,hrec] using H.gradient_mem_observedSpan
      have hd : r.direction∈H.observedSpan :=
        Submodule.subset_span (Or.inr ⟨r,by rw [hrec];exact List.mem_cons_self,Or.inl rfl⟩)
      exact H.observedSpan.add_mem (H.observedSpan.neg_mem hg) (H.observedSpan.smul_mem _ hd)
  · intro z
    trivial

end
end krylov.Methods
