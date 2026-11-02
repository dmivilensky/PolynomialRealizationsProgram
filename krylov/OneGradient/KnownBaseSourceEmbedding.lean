import krylov.OneGradient.KnownBaseSourceCube
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), complete physical source cube embedding.
Use: the uniform joint native remainder covers every original symmetric
physical prior/increment/output source, with no chosen-path restriction.
Source: existing finite source coordinates and exact actual positive-root
reconstruction in the known reference metric.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Information
  krylov.Correction krylov.Envelope
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The exact finite known-metric canonical coordinates of an original
physical source. The actual prior and output occupy distinct endpoint
slots when the full reference dimension is at least two.
Use: quantify the full physical source class in the existing source space.
Article: main_krylov, thm:local(b), actual full-source canonical tuple. -/
def knownBaseSourceTuple (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (S : Scenario (n+1)) :
    CanonicalScenario (n+1) (n+1) :=
  (fun i => relativeOperator base (S.increment i.val),fun j =>
    if j.val=0 then relativeOperator base (S.base-base)
    else if j.val=n then relativeOperator base S.terminal else 0)

/-- Every original symmetric physical source has a genuine member of
the existing symmetric finite source subspace with those exact coordinates.
Use: no larger or hypothetical source family is used in uniform upper bounds.
Article: main_krylov, thm:local(b), full physical source parameters.
Proof: true inverse-root congruence preserves symmetry of the original
prior difference, every actual query increment and the independent output. -/
def knownBaseSourceParameters
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (S : Scenario (n+1)) (hbase : S.base.IsSymm)
    (hinc : ∀ l<n,(S.increment l).IsSymm) (hterm : S.terminal.IsSymm) :
    symmetricScenarios (n+1) (n+1) :=
  ⟨knownBaseSourceTuple base S,⟨fun i => relativeOperator_isSymm base _ (hinc i.val i.isLt),fun j => by
    change (if j.val=0 then relativeOperator base (S.base-base)
      else if j.val=n then relativeOperator base S.terminal else 0).IsSymm
    split_ifs
    · exact relativeOperator_isSymm base _ (hbase.sub hb.1.isSymm)
    · exact relativeOperator_isSymm base _ hterm
    · exact Matrix.isSymm_zero⟩⟩

/-- The whole-source cube reconstructs the exact original physical
base, every real finite query increment and independent output form.
Use: joint uniform native estimates cover every actual original scenario,
including discontinuously selected matrices and scale-dependent sources.
Article: main_krylov, thm:local(b), exact full-source reconstruction.
Proof: actual finite endpoint selectors recover the distinct prior/output
slots. The genuine known positive root reconstructs each original physical
form exactly; adding back the known base cancels the prior difference. -/
theorem knownBaseSourceParameters_reconstruct
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef) (hn : 0<n)
    (S : Scenario (n+1)) (hbase : S.base.IsSymm)
    (hinc : ∀ l<n,(S.increment l).IsSymm) (hterm : S.terminal.IsSymm) :
    let Theta := knownBaseSourceParameters base hb S hbase hinc hterm
    (knownBaseSourceCube base Theta).base=S.base ∧
      (∀ l<n,(knownBaseSourceCube base Theta).increment l=S.increment l) ∧
      (knownBaseSourceCube base Theta).terminal=S.terminal := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · change base+metricRoot base*
      matrixSequenceExtension (n+1) (knownBaseSourceTuple base S).2 0*metricRoot base=S.base
    simp only [matrixSequenceExtension,dite_eq_left (by omega : 0<n+1),knownBaseSourceTuple,
      ite_true,relativeOperator_reconstruct base _ hb]
    abel
  · intro l hl
    change metricRoot base*matrixSequenceExtension n (knownBaseSourceTuple base S).1 l*metricRoot base=S.increment l
    simp only [matrixSequenceExtension,dite_eq_left hl,knownBaseSourceTuple,relativeOperator_reconstruct base _ hb]
  · change metricRoot base*matrixSequenceExtension (n+1) (knownBaseSourceTuple base S).2 n*metricRoot base=S.terminal
    simp only [matrixSequenceExtension,dite_eq_left (by omega : n<n+1),knownBaseSourceTuple,
      ite_eq_right (Nat.ne_of_gt hn),ite_true,relativeOperator_reconstruct base _ hb]

/-- Reconstructed source parameters give exactly the original extended
query/output matrix family at every slot, including the independent output.
Use: native expansion and uniform tube statements transfer to the whole
physical source class with their actual complete histories and decisions.
Article: main_krylov, thm:local(b), exact all-source native operator coverage.
Proof: original and reconstructed sources have the same base, every true
finite increment and independent output. Their actual finite probe sums
and output extension therefore coincide at every index. -/
theorem knownBaseSourceParameters_operators
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef) (hn : 0<n)
    (S : Scenario (n+1)) (hbase : S.base.IsSymm)
    (hinc : ∀ l<n,(S.increment l).IsSymm) (hterm : S.terminal.IsSymm) :
    let Theta := knownBaseSourceParameters base hb S hbase hinc hterm
    oneGradientScenarioMatrices (knownBaseSourceCube base Theta) n=oneGradientScenarioMatrices S n := by
  let Theta := knownBaseSourceParameters base hb S hbase hinc hterm
  let T := knownBaseSourceCube base Theta
  have hrec := knownBaseSourceParameters_reconstruct base hb hn S hbase hinc hterm
  have hprobe (k : ℕ) (hk : k≤n) : T.probe k=S.probe k := by
    change T.base+∑ l∈range k,T.increment l=S.base+∑ l∈range k,S.increment l
    rw [hrec.1]
    congr 1
    exact sum_congr rfl (fun l hl => hrec.2.1 l ((mem_range.mp hl).trans_le hk))
  funext j
  by_cases hj : j≤n
  · rw [oneGradientScenarioMatrices_probe T n j hj,oneGradientScenarioMatrices_probe S n j hj,hprobe j hj]
  · change (if j≤n then T.probe j else T.probe n+T.terminal)=
      if j≤n then S.probe j else S.probe n+S.terminal
    rw [ite_eq_right hj,ite_eq_right hj,hprobe n le_rfl,hrec.2.2]

/-- One common actual known-metric bound for every original source form
bounds its full finite parameter tuple by the same number.
Use: a source-wide small-budget family enters the common cubic remainder
ball uniformly, without a path-dependent or dimension-dependent norm change.
Article: main_krylov, thm:local(b), genuine full-source parameter norm.
Proof: the existing source norm is the true product/supremum norm of its
finite matrix arrays. Every query coordinate has its original bound; the
second array selects only the actual prior, output or zero. -/
theorem knownBaseSourceParameters_norm_le
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (S : Scenario (n+1)) (hbase : S.base.IsSymm)
    (hinc : ∀ l<n,(S.increment l).IsSymm) (hterm : S.terminal.IsSymm)
    (v : ℝ) (hv : 0≤v)
    (hprior : relativeBudget base (S.base-base)≤v)
    (hquery : ∀ l<n,relativeBudget base (S.increment l)≤v)
    (houtput : relativeBudget base S.terminal≤v) :
    ‖knownBaseSourceParameters base hb S hbase hinc hterm‖≤v := by
  change ‖knownBaseSourceTuple base S‖≤v
  rw [Prod.norm_def,max_le_iff]
  constructor
  · apply (pi_norm_le_iff_of_nonneg hv).mpr
    intro i
    exact hquery i.val i.isLt
  · apply (pi_norm_le_iff_of_nonneg hv).mpr
    intro j
    change ‖if j.val=0 then relativeOperator base (S.base-base)
      else if j.val=n then relativeOperator base S.terminal else 0‖≤v
    split_ifs
    · exact hprior
    · exact houtput
    · simpa only [norm_zero] using hv

end
end krylov.OneGradient
