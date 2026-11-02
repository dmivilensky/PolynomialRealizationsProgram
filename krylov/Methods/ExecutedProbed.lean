import krylov.Methods.DirectionReindex
import krylov.Methods.RFCProjection

/-!
Article: main_krylov, def:classes(M), alg:fc and lem:U(d), genuine probed trajectories.
Use: expose fixed chronological coordinates of the real executed histories,
including every actual correction movement and its observed secant difference.
Source: the existing nonanticipating method executor and executed-pair indexing.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual probed-policy iteration records exactly one total evaluated step.
Use: retention lengths depend on the true iteration number, independently of correction counts.
Article: main_krylov, def:classes(M) and alg:fc.
Proof: the actual executor prepends exactly one iteration record. -/
theorem methodRun_length (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    (methodRun m A B g k).records.length=k := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg Nat.succ ih

/-- The actual gradient observed after a full probed-policy iteration prefix.
Use: RFC regularity follows real returned gradients, including corrections.
Article: main_krylov, alg:fc, g_k. -/
def probedGradient (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  (methodRun m A B g k).gradient

/-- The actual correction result returned by a probed policy at its next real iteration.
Use: no model residual or externally assigned movement replaces the executed query tree.
Article: main_krylov, def:classes(M), actual correction phase. -/
def probedPhase (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : CorrectionResult E :=
  let H := methodRun m A B g k
  let d := m.direction H
  runCorrections (m.correction H (A k d)) (B k) (searchedGradient H.gradient d (A k d))

/-- The total line-plus-correction step actually recorded by a probed policy.
Use: fixed-coordinate models use true physical displacements.
Article: main_krylov, alg:fc, s_k=α_kd_k+Σχ_k. -/
def probedStep (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  let H := methodRun m A B g k
  let d := m.direction H
  lineLength H.gradient d (A k d) • d+(probedPhase m A B g k).movement

/-- The actual recorded probed-policy secant is its real consecutive observed-gradient difference.
Use: correction-contaminated RFC pairs are never replaced by fictitious line-operator images.
Article: main_krylov, alg:fc, y_k=g_(k+1)−g_k. -/
def probedSecant (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  probedGradient m A B g (k+1)-probedGradient m A B g k

/-- The next actual probed-policy gradient is precisely its real correction-phase result.
Use: the finite regularity induction propagates the actual query executor's output.
Article: main_krylov, lem:U(d), observed-gradient update.
Proof: both sides read the same gradient field of the newly executed iteration record. -/
theorem probedGradient_succ (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    probedGradient m A B g (k+1)=(probedPhase m A B g k).gradient := rfl

/-- The actual recorded probed-policy secant defect is exactly the true correction-operator mismatch applied to the real total correction movement.
Use: asymptotic pair estimates concern the genuine recorded y_k and total physical s_k.
Article: main_krylov, apD:eq:pairs, actual recorded-pair identity.
Proof: specialize the exact actual line/correction balance to the real
executed query tree, then subtract the line operator applied to its actual total step. -/
theorem probedSecant_defect_identity (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    probedSecant m A B g k-A k (probedStep m A B g k)=(B k-A k) (probedPhase m A B g k).movement := by
  let H := methodRun m A B g k
  let d := m.direction H
  have he := correction_pair_identity (A k) (B k) H.gradient
    (lineLength H.gradient d (A k d) • d) (m.correction H (A k d))
  simp only [map_smul] at he
  change probedSecant m A B g k=A k (probedStep m A B g k)+(B k-A k) (probedPhase m A B g k).movement at he
  rw [he]
  abel

/-- Every actual probed execution has exactly its true chronological total-step/secant transcript.
Use: fixed finite coordinate solves describe the real RFC history, including all actual correction phases.
Article: main_krylov, lem:U(d), actual stored-pair coordinates.
Proof: the actual iteration record stores its total line-plus-correction step
and its real next gradient; pair extraction subtracts precisely the real preceding gradient. -/
theorem methodRun_pairs_executed (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    (methodRun m A B g k).pairs=executedPairs (probedStep m A B g) (probedSecant m A B g) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (probedStep m A B g k,probedSecant m A B g k)::(methodRun m A B g k).pairs=_
    rw [ih]
    rfl

/-- Every actual retained probed window is its prescribed newest prefix of the real executed-pair transcript.
Use: full, sliding and restarted policy regularity use the same exact finite coordinate bridge.
Article: main_krylov, alg:fc and lem:U(d), retained actual histories.
Proof: substitute the proved real iteration count and actual complete pair transcript. -/
theorem selectedWindow_methodRun (memory : ℕ → ℕ) (m : ProbedMethod E)
    (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    selectedWindow memory (methodRun m A B g k)=
      (executedPairs (probedStep m A B g) (probedSecant m A B g) k).take (memory k) := by
  change (methodRun m A B g k).pairs.take (memory (methodRun m A B g k).records.length)=_
  rw [methodRun_length,methodRun_pairs_executed]

omit [InnerProductSpace ℝ E] in
/-- Any genuine history with the stated executed-pair transcript has exactly its prescribed fixed-length retained window.
Use: analytic history families are coordinated by their actual observed pairs, without imposing a norm on history records.
Article: main_krylov, lem:U(d), finite observed-data charts.
Proof: pair extraction preserves the actual record count; substitute the
proved chronological transcript before applying the genuine retention rule. -/
theorem selectedWindow_of_executed_pairs (memory : ℕ → ℕ) (H : History E) (s y : ℕ → E) (k : ℕ)
    (hp : H.pairs=executedPairs s y k) :
    selectedWindow memory H=(executedPairs s y k).take (memory k) := by
  have hl : H.records.length=k := by rw [← H.pairs_length,hp,executedPairs_length]
  change H.pairs.take (memory H.records.length)=_
  rw [hl,hp]

end
end krylov.Methods
