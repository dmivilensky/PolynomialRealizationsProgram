import krylov.Information.NormalizedLower
import krylov.Correction.CompactScenarioBounds

/-!
Article: main_krylov, thm:C, the original physical admissible-scenario bridge.
Use: represent every original physical scenario by exactly its finite
own-base canonical variables and preserve the genuine complete method output.
Source: actual inverse-root relative forms, true reconstruction identities
and the existing finite-horizon nonanticipating oracle congruence theorem.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant krylov.Envelope
  krylov.Methods krylov.Stability krylov.Correction krylov.Variation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The true finite canonical parameter arrays of an original physical scenario, using its actual own base.
Use: all original increments, independent intermediate defects and the terminal defect retain precisely their source budgets.
Article: main_krylov, thm:C, finite canonical coordinates of Ξ. -/
def Scenario.canonicalParameters (S : Scenario n) (N : ℕ) : CanonicalScenario n (N+1) :=
  (fun i => relativeOperator S.base (S.increment i.val),
   fun i => relativeOperator S.base (if i.val<N then S.correction i.val else S.terminal))

/-- The true finite canonical parameters of a symmetric original scenario belong to the actual symmetric source space.
Use: apply the joint original-scenario compact tube to physical source data without adding a symmetry hypothesis on a chart.
Article: main_krylov, thm:C, actual symmetric canonical source coordinates.
Proof: genuine inverse-root normalization preserves every actual symmetric
increment and defect, and the final finite coordinate selects exactly the
source terminal perturbation.
-/
def Scenario.symmetricParameters (S : Scenario n) (N : ℕ)
    (hE : ∀ i<N, (S.increment i).IsSymm) (hT : S.terminal.IsSymm)
    (hF : ∀ i<N, (S.correction i).IsSymm) : symmetricScenarios n (N+1) :=
  ⟨S.canonicalParameters N,by
    constructor
    · intro i
      exact relativeOperator_isSymm _ _ (hE i.val (by omega))
    · intro i
      change (relativeOperator S.base (if i.val<N then S.correction i.val else S.terminal)).IsSymm
      split_ifs with hi
      · exact relativeOperator_isSymm _ _ (hF _ hi)
      · exact relativeOperator_isSymm _ _ hT⟩

/-- Each actual meaningful extended canonical increment is exactly the relative form of its original physical increment.
Use: reconstruct the true finite physical probe sequence without shifting any index or budget.
Article: main_krylov, thm:C, exact finite increment coordinate.
Proof: the true zero extension reads the meaningful finite coordinate. -/
theorem Scenario.canonicalParameters_increment (S : Scenario n) (N : ℕ) {i : ℕ} (hi : i<N) :
    matrixSequenceExtension N (S.canonicalParameters N).1 i=relativeOperator S.base (S.increment i) := by
  simp only [matrixSequenceExtension,dite_eq_left hi,Scenario.canonicalParameters]

/-- Every actual meaningful canonical correction coordinate selects precisely the original intermediate or terminal perturbation.
Use: preserve the true source distinction between F_k and E′ at the actual final query.
Article: main_krylov, thm:C, exact finite correction coordinate.
Proof: the actual finite horizon includes its true final coordinate, whose
conditional selects E′ rather than an extra intermediate defect. -/
theorem Scenario.canonicalParameters_correction (S : Scenario n) (N : ℕ) {i : ℕ} (hi : i≤N) :
    matrixSequenceExtension (N+1) (S.canonicalParameters N).2 i=
      relativeOperator S.base (if i<N then S.correction i else S.terminal) := by
  simp only [matrixSequenceExtension,dite_eq_left (by omega : i<N+1),Scenario.canonicalParameters]

/-- The genuine canonical parameter chart reconstructs every actually queried physical probe operator exactly.
Use: the all-scenario compact upper estimate concerns the original physical execution.
Article: main_krylov, thm:C, A_k in exact own-base canonical coordinates.
Proof: each original relative increment reconstructs its actual physical
matrix through the true positive root. Distribute that congruence over the
actual finite probe prefix and retain the genuine physical base.
-/
theorem Scenario.canonicalParameters_probe (S : Scenario n) (N : ℕ) (hS : S.base.PosDef)
    {k : ℕ} (hk : k≤N) :
    scenarioProbe S.base (S.canonicalParameters N) k=S.probeOracle k := by
  -- Reconstruct every actual increment before summing its true chronological prefix.
  have hsum : metricRoot S.base*(∑ i∈range k, matrixSequenceExtension N (S.canonicalParameters N).1 i)*
      metricRoot S.base=∑ i∈range k, S.increment i := by
    rw [Matrix.mul_sum,Matrix.sum_mul]
    exact sum_congr rfl fun i hi => by
      rw [S.canonicalParameters_increment N (by have := mem_range.mp hi; omega)]
      exact relativeOperator_reconstruct _ _ hS
  simp only [scenarioProbe,canonicalFCPath,cumulativeDrift,one_smul]
  change cgOperator S.base + (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ))
    (metricRoot S.base*(∑ i∈range k, matrixSequenceExtension N (S.canonicalParameters N).1 i)*metricRoot S.base)=_
  rw [hsum]
  exact (map_add (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) _ _).symm

/-- The same true finite canonical parameters reconstruct every actual intermediate and terminal physical correction operator.
Use: the original all-budget output is preserved through its actual last correction.
Article: main_krylov, thm:C, B_k in exact own-base canonical coordinates.
Proof: the true finite correction coordinate reads F_k before the terminal
index and E′ at it. Its actual positive-root congruence reconstructs that
physical perturbation and adds it to the reconstructed actual probe.
-/
theorem Scenario.canonicalParameters_correctionOracle (S : Scenario n) (N : ℕ) (hS : S.base.PosDef)
    {k : ℕ} (hk : k≤N) :
    scenarioCorrection S.base (S.canonicalParameters N) k=S.correctionOracle N k := by
  -- Reconstruct the actual independent perturbation on the same own-base metric.
  have hF : metricRoot S.base*matrixSequenceExtension (N+1) (S.canonicalParameters N).2 k*
      metricRoot S.base=(if k<N then S.correction k else S.terminal) := by
    rw [S.canonicalParameters_correction N hk]
    exact relativeOperator_reconstruct _ _ hS
  rw [scenarioCorrection,S.canonicalParameters_probe N hS hk,hF]
  change cgOperator (S.probe k)+cgOperator (if k<N then S.correction k else S.terminal)=_
  dsimp only [cgOperator]
  rw [← map_add]
  by_cases hi : k<N
  · simp only [hi,ite_true,Scenario.correctionOracle,Scenario.intermediate,cgOperator]
  · simp only [hi,ite_false,Scenario.correctionOracle,cgOperator]
    have he : k=N := by omega
    subst k
    rfl

/-- Every actual finite canonical scenario reconstruction returns exactly the original physical method gradient.
Use: transfer the common compact canonical bound to the supremum over all original physical admissible scenarios.
Article: main_krylov, thm:C, exact finite source-output bridge.
Proof: both genuine query operator families agree at every actual iteration
before the finite output horizon. The existing complete-history prefix
congruence theorem preserves the real method output, for arbitrary policies.
-/
theorem Scenario.canonicalParameters_output (S : Scenario n) (N : ℕ) (hS : S.base.PosDef)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (g : EuclideanSpace ℝ (Fin n)) :
    probedGradient m (scenarioProbe S.base (S.canonicalParameters N))
      (scenarioCorrection S.base (S.canonicalParameters N)) g (N+1)=
        probedGradient m S.probeOracle (S.correctionOracle N) g (N+1) :=
  congrArg History.gradient (methodRun_congr_prefix m _ _ _ _ g (N+1)
    (fun k hk => S.canonicalParameters_probe N hS (by omega))
    (fun k hk => S.canonicalParameters_correctionOracle N hS (by omega)))

/-- Every original admissible physical scenario obeys the true common-budget norm bound in its exact symmetric finite canonical coordinates.
Use: the compact radius is imposed only through the original independent physical budgets.
Article: main_krylov, thm:C, actual largest-budget control of the finite source chart.
Proof: each finite increment norm is its genuine original relative budget;
each correction coordinate selects exactly its genuine intermediate or
terminal relative budget. Their actual finite product maximum is at most μ.
-/
theorem Scenario.symmetricParameters_norm_le (S : Scenario n) (N : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) (ω : ℕ → ℝ) (w τ : ℝ)
    (hS : S.Admissible N A r ω w τ) {μ : ℝ} (hμ : 0≤μ)
    (hω : ∀ i<N, ω i≤μ) (hw : w≤μ) (hτ : τ≤μ) :
    ‖S.symmetricParameters N (fun i hi => (hS.2.2.1 i hi).1) hS.2.2.2.1
      (fun i hi => (hS.2.2.2.2.2 i hi).1)‖≤μ := by
  -- Use the same original individual physical budgets at every actual finite coordinate.
  apply symmetricScenario_norm_le _ hμ
  · intro i
    change relativeBudget S.base (S.increment i.val)≤μ
    exact ((hS.2.2.1 i.val (by omega)).2).trans (hω i.val (by omega))
  · intro i
    change ‖relativeOperator S.base (if i.val<N then S.correction i.val else S.terminal)‖≤μ
    split_ifs with hi
    · exact ((hS.2.2.2.2.2 i.val hi).2).trans hτ
    · exact hS.2.2.2.2.1.trans hw

end
end krylov.Information
