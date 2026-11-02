import krylov.Information.TwinReplay
import krylov.Methods.QuadraticConsistency
import krylov.Methods.ReferenceProbedSteps

/-!
Article: main_krylov, s4:cor-Q, genuine common pre-quadratic prefix geometry.
Use: primitive agreement of actual reference-direction probe actions forces
all globally CG-consistent methods to share the real CG steps, gradients,
measured pairs and direction flag, with zero actual intermediate queries.
Source: the proved full-history nonanticipating shadow induction, genuine
quadratic consistency and true exact-search direction-scale cancellation.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The original pre-quadratic source condition: actual probes agree with one genuine quadratic reference only on its real chronological CG directions.
Use: the common observed prefix is derived from primitive physical oracle actions, rather than assumed.
Article: main_krylov, s4:cor-Q, the original scenario class Q. -/
def Scenario.PreQuadratic (S : Scenario n) (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) : Prop :=
  ∀ k<N, S.probeOracle k (CG.direction Q g k)=Q (CG.direction Q g k)

/-- Every actual globally CG-consistent method follows its complete genuine quadratic reference history on a pre-quadratic source prefix.
Use: no restriction on the independently chosen true intermediate correction operators is needed.
Article: main_krylov, s4:cor-Q, actual common pre-quadratic prefix.
Proof: the original probe condition is exactly the genuine CG shadow induction premise; actual reference correction queries vanish. -/
theorem Scenario.PreQuadratic.run {S : Scenario n}
    {Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {g : EuclideanSpace ℝ (Fin n)} {N : ℕ} (h : S.PreQuadratic Q g N)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v≠0 → 0 < inner ℝ v (Q v))
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m)
    {k : ℕ} (hk : k≤N) :
    methodRun m S.probeOracle (S.correctionOracle N) g k=methodRun m (fun _ => Q) (fun _ => Q) g k :=
  cgConsistent_shadow m hm Q hQ hpos S.probeOracle (S.correctionOracle N) g N h k hk

/-- Every actual globally CG-consistent method has exactly the genuine common CG gradient throughout the pre-quadratic source prefix.
Use: the actual incoming state before the final nonquadratic probe is common across the full source method class.
Article: main_krylov, s4:cor-Q, actual common pre-quadratic prefix.
Proof: the proved actual complete-history shadow and genuine quadratic gradient identity give the real observed gradient. -/
theorem Scenario.PreQuadratic.gradient {S : Scenario n}
    {Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {g : EuclideanSpace ℝ (Fin n)} {N : ℕ} (h : S.PreQuadratic Q g N)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v≠0 → 0 < inner ℝ v (Q v))
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m)
    {k : ℕ} (hk : k≤N) : probedGradient m S.probeOracle (S.correctionOracle N) g k=CG.gradient Q g k := by
  change (methodRun m _ _ _ _).gradient=_
  rw [h.run hQ hpos m hm hk]
  exact quadratic_gradient_eq_cg m hm Q hQ hpos g k

/-- Every actual globally CG-consistent method chooses a strictly positive multiple of the same real CG reference direction throughout the pre-quadratic prefix, including the last direction.
Use: the common direction flag is proved for the original full method class without a policy regularity premise.
Article: main_krylov, s4:cor-Q, actual common pre-quadratic prefix.
Proof: actual complete-history shadow identifies the reference decision state, where true global CG consistency supplies its original positive scale. -/
theorem Scenario.PreQuadratic.direction {S : Scenario n}
    {Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {g : EuclideanSpace ℝ (Fin n)} {N : ℕ} (h : S.PreQuadratic Q g N)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v≠0 → 0 < inner ℝ v (Q v))
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m)
    {k : ℕ} (hk : k≤N) :
    ∃ c : ℝ, 0<c ∧ probedDirection m S.probeOracle (S.correctionOracle N) g k=c • CG.direction Q g k := by
  obtain ⟨c,hc,hd,_⟩ := hm Q hQ hpos g k
  refine ⟨c,hc,?_⟩
  change m.direction (methodRun m _ _ _ _)=_
  rw [h.run hQ hpos m hm hk]
  exact hd

/-- Every genuine preterminal evaluated step of every globally CG-consistent method equals the original common physical CG reference step.
Use: all true measured stored step arrays are common, despite method-dependent positive direction scales.
Article: main_krylov, s4:cor-Q, actual common pre-quadratic prefix.
Proof: extract the latest actual evaluated-step record from the equal genuine successor histories, then use the proved true quadratic step identity. -/
theorem Scenario.PreQuadratic.step {S : Scenario n}
    {Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {g : EuclideanSpace ℝ (Fin n)} {N : ℕ} (h : S.PreQuadratic Q g N)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v≠0 → 0 < inner ℝ v (Q v))
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m)
    {k : ℕ} (hk : k<N) :
    probedStep m S.probeOracle (S.correctionOracle N) g k=referenceStep Q g k := by
  have he := congrArg (fun H : History (EuclideanSpace ℝ (Fin n)) =>
    (H.records.getD 0 ⟨0,0,0,0,[]⟩).step) (h.run hQ hpos m hm (Nat.succ_le_iff.mpr hk))
  have hs : probedStep m S.probeOracle (S.correctionOracle N) g k=probedStep m (fun _ => Q) (fun _ => Q) g k := he
  exact hs.trans (quadratic_probedStep_eq_cg m hm Q hQ hpos g k)

/-- Every actual preterminal measured secant of every globally CG-consistent method is the reference operator applied to the same genuine CG physical step.
Use: real pair histories coincide across all methods; hypothetical exact line-image substitutions are unnecessary.
Article: main_krylov, s4:cor-Q, actual common pre-quadratic prefix.
Proof: both true consecutive gradients equal their genuine CG values. The actual reference gradient update gives precisely the displayed physical secant. -/
theorem Scenario.PreQuadratic.secant {S : Scenario n}
    {Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {g : EuclideanSpace ℝ (Fin n)} {N : ℕ} (h : S.PreQuadratic Q g N)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v≠0 → 0 < inner ℝ v (Q v))
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m)
    {k : ℕ} (hk : k<N) :
    probedSecant m S.probeOracle (S.correctionOracle N) g k=Q (referenceStep Q g k) := by
  unfold probedSecant
  rw [h.gradient hQ hpos m hm (Nat.succ_le_iff.mpr hk),h.gradient hQ hpos m hm hk.le]
  change searchedGradient (CG.gradient Q g k) (CG.direction Q g k) (Q (CG.direction Q g k))-CG.gradient Q g k=_
  simp only [searchedGradient,referenceStep,map_smul]
  abel

/-- Every actual stored-pair transcript of every globally CG-consistent method is exactly the common genuine quadratic CG pair transcript on a pre-quadratic source prefix.
Use: the actual latest models and observed spans use the same true physical stored data for all competing policies.
Article: main_krylov, s4:cor-Q, actual common pre-quadratic prefix.
Proof: the actual executor records its true total steps and measured secants. Both have their independently proved common CG values; induction gives the genuine original reference pair recursion. -/
theorem Scenario.PreQuadratic.pairs {S : Scenario n}
    {Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {g : EuclideanSpace ℝ (Fin n)} {N : ℕ} (h : S.PreQuadratic Q g N)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v≠0 → 0 < inner ℝ v (Q v))
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m) :
    ∀ k≤N, (methodRun m S.probeOracle (S.correctionOracle N) g k).pairs=referencePairs Q g k := by
  -- Preserve the actual original measured step/secant pair at each true chronological successor.
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [methodRun_pairs_executed]
    change (probedStep m S.probeOracle (S.correctionOracle N) g k,
      probedSecant m S.probeOracle (S.correctionOracle N) g k)::executedPairs _ _ k=_
    rw [h.step hQ hpos m hm (by omega),h.secant hQ hpos m hm (by omega),← methodRun_pairs_executed,
      ih (by omega)]
    rfl

/-- Every actual preterminal correction query of every globally CG-consistent method on a pre-quadratic source scenario is zero.
Use: the original H4 admissibility constraint is vacuous on this genuine common information regime.
Article: main_krylov, s4:cor-Q, actual common pre-quadratic prefix.
Proof: the real prefix history is the quadratic one. The original matching probe condition transports through its positive direction scale, so the actual correction decision tree is exactly the genuine zero-query reference tree. -/
theorem Scenario.PreQuadratic.correctionQuery_zero {S : Scenario n}
    {Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {g : EuclideanSpace ℝ (Fin n)} {N : ℕ} (h : S.PreQuadratic Q g N)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v≠0 → 0 < inner ℝ v (Q v))
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m)
    {k : ℕ} (hk : k<N) : S.correctionQuery N m g k=0 := by
  -- Actual quadratic consistency gives the original zero correction tree before any independent physical correction answer.
  obtain ⟨c,hc,hd,hzero⟩ := hm Q hQ hpos g k
  let H := methodRun m (fun _ => Q) (fun _ => Q) g k
  have hp : S.probeOracle k (m.direction H)=Q (m.direction H) := by
    rw [hd,map_smul,map_smul,h k hk]
  unfold Scenario.correctionQuery probedProbe probedDirection
  rw [h.run hQ hpos m hm hk.le]
  rw [hp]
  change firstCorrectionStep (m.correction H (Q (m.direction H)))=0
  generalize he : m.correction H (Q (m.direction H))=tree at hzero ⊢
  cases tree with
  | done => rfl
  | query u next => exact hzero.1


/-- The actual entire direction flag of every globally CG-consistent method on a pre-quadratic source prefix is exactly the common original CG direction flag.
Use: the observation-preserving twin geometry is common to the entire original method class.
Article: main_krylov, s4:cor-Q, actual common pre-quadratic prefix.
Proof: each actual raw direction is its genuine reference direction times a positive real unit. Span inclusion in both directions follows by multiplying by that scalar or its true inverse. -/
theorem Scenario.PreQuadratic.flag {S : Scenario n}
    {Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {g : EuclideanSpace ℝ (Fin n)} {N : ℕ} (h : S.PreQuadratic Q g N)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v≠0 → 0 < inner ℝ v (Q v))
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m)
    {k : ℕ} (hk : k≤N) :
    executedDirectionSpan m S.probeOracle (S.correctionOracle N) g k=
      Submodule.span ℝ (CG.direction Q g '' Set.Iic k) := by
  -- Positive actual reference scales preserve exactly the genuine chronological direction span.
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    obtain ⟨c,_,hd⟩ := h.direction hQ hpos m hm (hi.trans hk)
    rw [hd]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,hi,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    obtain ⟨c,hc,hd⟩ := h.direction hQ hpos m hm (hi.trans hk)
    have hdir : CG.direction Q g i=c⁻¹ • probedDirection m S.probeOracle (S.correctionOracle N) g i := by
      rw [hd,smul_smul,inv_mul_cancel₀ hc.ne',one_smul]
    rw [hdir]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,hi,rfl⟩)

end
end krylov.Information

