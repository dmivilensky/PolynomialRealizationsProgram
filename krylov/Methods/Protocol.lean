import krylov.Reference.CG
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
Article: main_krylov, def:classes(M) and lem:terminal-fibre, nonanticipating observations.
Use: directions and corrections receive only actual prior observations; a finite
correction decision tree permits any finite adaptive number of correction probes.
Source: the article's information protocol, instantiated with the concrete CG recurrence.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A finite adaptive correction protocol: query a displacement, observe its new gradient and continue.
Use: includes arbitrary finite repeated corrections without exposing the unknown operator.
Article: main_krylov, def:classes(M), optional repeated correction probes. -/
inductive CorrectionTree (E : Type*) where
  /-- Finish the correction phase without another operator query. -/
  | done : CorrectionTree E
  /-- Query a displacement; only its observed new gradient chooses the next finite subtree. -/
  | query (step : E) (next : E → CorrectionTree E) : CorrectionTree E

/-- The actual displacement, final gradient and full observed trace of a correction phase.
Use: all queries remain available to future decisions, so transcript equality enforces nonanticipation.
Article: main_krylov, def:classes(M), correction observations. -/
structure CorrectionResult (E : Type*) where
  /-- Sum of all actual correction displacements. -/
  movement : E
  /-- The actual gradient after the last correction query. -/
  gradient : E
  /-- Actual queried displacements paired with their actually observed gradients, in query order. -/
  trace : List (E × E)

/-- Execute the actual finite correction decision tree against the actual segment operator.
Use: subsequent decisions see actual gradients, and each displacement queries its prescribed operator once.
Article: main_krylov, def:classes(M), repeated correction execution. -/
def runCorrections (p : CorrectionTree E) (B : E →L[ℝ] E) (g : E) : CorrectionResult E :=
  match p with
  | .done => ⟨0, g, []⟩
  | .query u next =>
      let gnew := g+B u
      let r := runCorrections (next gnew) B gnew
      ⟨u+r.movement, r.gradient, (u,gnew)::r.trace⟩

/-- Every actual correction displacement along this executed finite decision tree is zero.
Use: this is the article's quadratic consistency condition on actual correction queries.
Article: main_krylov, def:classes(M), w_k=0. -/
def ZeroCorrections (p : CorrectionTree E) (B : E →L[ℝ] E) (g : E) : Prop :=
  match p with
  | .done => True
  | .query u next => u=0 ∧ ZeroCorrections (next (g+B u)) B (g+B u)

/-- Zero corrections on a quadratic transcript remain zero under every actual correction operator.
Use: all finite repeated correction queries preserve indistinguishability of the planar prefix.
Article: main_krylov, lem:terminal-fibre, preceding zero corrections.
Proof: induction on the actual decision tree; every zero query returns the same
gradient under both operators and therefore selects the same actual next subtree. -/
theorem zeroCorrections_change_operator (p : CorrectionTree E) (B C : E →L[ℝ] E) (g : E)
    (hp : ZeroCorrections p B g) :
    runCorrections p B g=runCorrections p C g ∧
      (runCorrections p C g).movement=0 ∧ (runCorrections p C g).gradient=g := by
  -- A zero query returns the same actual gradient and selects the same continuation subtree.
  induction p generalizing g with
  | done => exact ⟨rfl, rfl, rfl⟩
  | query u next ih =>
    obtain ⟨hu, hn⟩ := hp
    subst u
    simp only [map_zero, add_zero] at hn
    obtain ⟨he, hm, hg⟩ := ih g g hn
    simp only [runCorrections, map_zero, add_zero, zero_add]
    rw [he, hm, hg]
    exact ⟨rfl, rfl, rfl⟩

/-- One full observed iteration, including all finite intermediate correction queries.
Use: no information available to the method is discarded by the history model.
Article: main_krylov, def:classes(M), D_k. -/
structure IterationRecord (E : Type*) where
  /-- The actual direction chosen before receiving its probe. -/
  direction : E
  /-- The actual operator action revealed by the line-search probe. -/
  probe : E
  /-- The total evaluated step, including all actual correction displacements. -/
  step : E
  /-- The actual next gradient after the complete correction phase. -/
  gradient : E
  /-- Every actual intermediate correction observation. -/
  corrections : List (E × E)

/-- Complete observed past, with the most recent iteration first and the initial gradient retained.
Use: a nonanticipating policy receives only this data and its current probe.
Article: main_krylov, def:classes(M), D_0 and D_k. -/
structure History (E : Type*) where
  /-- Initial observed gradient, independent of unknown future operators. -/
  initial : E
  /-- Full past iteration records, with the most recent first. -/
  records : List (IterationRecord E)

/-- The current actual observed gradient, read from the complete actual history.
Use: the line-search scalar and correction oracle use this data-only quantity.
Article: main_krylov, def:classes(M), g_k. -/
def History.gradient (H : History E) : E :=
  match H.records with | [] => H.initial | r::_ => r.gradient

/-- A genuinely nonanticipating probed policy with arbitrary finite adaptive correction phases.
Use: fixed prior parameters may be captured by either decision function, but the unknown operator is absent.
Article: main_krylov, def:classes(M), direction and correction decision rules. -/
structure ProbedMethod (E : Type*) where
  /-- Choose the direction using only the full observed past. -/
  direction : History E → E
  /-- Choose a finite adaptive correction protocol using only the observed past and current probe. -/
  correction : History E → E → CorrectionTree E

/-- Execute a real iteration with its actual search operator and actual correction operator.
Use: every observed gradient is generated by the prescribed real oracle updates.
Article: main_krylov, def:classes(M), steps (1)–(4). -/
def methodAdvance (m : ProbedMethod E) (A B : E →L[ℝ] E) (H : History E) : History E :=
  let d := m.direction H
  let z := A d
  let r := runCorrections (m.correction H z) B (searchedGradient H.gradient d z)
  ⟨H.initial, ⟨d,z,lineLength H.gradient d z • d+r.movement,r.gradient,r.trace⟩::H.records⟩

/-- The actual run of a nonanticipating probed method on an actual operator sequence.
Use: all information-fibre assertions compare actual executed histories.
Article: main_krylov, def:classes(M), adaptive trajectory. -/
def methodRun (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) : ℕ → History E
  | 0 => ⟨g, []⟩
  | k+1 => methodAdvance m (A k) (B k) (methodRun m A B g k)

/-- Quadratic CG consistency is a condition on the actual method run and actual concrete CG directions.
Use: consistency is quantified over static positive operators, not built into a presumed data-fibre response.
Article: main_krylov, def:classes(M), directions are positive multiples of CG and corrections vanish. -/
def CGConsistent (m : ProbedMethod E) : Prop :=
  ∀ (Q : E →L[ℝ] E), Q.toLinearMap.IsSymmetric → (∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) → ∀ g k,
    let H := methodRun m (fun _ => Q) (fun _ => Q) g k
    ∃ scale : ℝ, 0<scale ∧ m.direction H=scale • (cgRun Q g k).direction ∧
      ZeroCorrections (m.correction H (Q (m.direction H))) Q
        (searchedGradient H.gradient (m.direction H) (Q (m.direction H)))

/-- A real iteration preserves the complete actual quadratic history whenever its actual search probe agrees.
Use: prefix indistinguishability covers all finite intermediate correction queries.
Article: main_krylov, lem:terminal-fibre, nonanticipating induction step.
Proof: the common actual search probe selects the same decision tree; its quadratic
zero-query execution is invariant under the actual correction operator by the proved tree induction. -/
theorem methodAdvance_shadow (m : ProbedMethod E) (A B Q : E →L[ℝ] E) (H : History E)
    (hprobe : A (m.direction H)=Q (m.direction H))
    (hz : ZeroCorrections (m.correction H (Q (m.direction H))) Q
      (searchedGradient H.gradient (m.direction H) (Q (m.direction H)))) :
    methodAdvance m A B H=methodAdvance m Q Q H := by
  have he := (zeroCorrections_change_operator _ Q B _ hz).1
  simp only [methodAdvance, hprobe]
  rw [← he]

/-- The full actual method histories agree with a quadratic shadow throughout any matching-probe prefix.
Use: every subsequent decision is forced by actual observed data, regardless of its internal policy.
Article: main_krylov, lem:terminal-fibre, complete observed prefix equality.
Proof: finite induction applies the proved actual iteration shadow lemma on the
actual common history; all directions, correction queries and gradients remain equal. -/
theorem methodRun_shadow (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E)
    (Q : E →L[ℝ] E) (g : E) (N : ℕ)
    (h : ∀ k<N,
      let H := methodRun m (fun _ => Q) (fun _ => Q) g k
      A k (m.direction H)=Q (m.direction H) ∧
        ZeroCorrections (m.correction H (Q (m.direction H))) Q
          (searchedGradient H.gradient (m.direction H) (Q (m.direction H)))) :
    ∀ k≤N, methodRun m A B g k=methodRun m (fun _ => Q) (fun _ => Q) g k := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [methodRun, methodRun, ih ((Nat.le_succ k).trans hk)]
    exact methodAdvance_shadow m _ _ _ _ (h k (Nat.lt_of_succ_le hk)).1
      (h k (Nat.lt_of_succ_le hk)).2

end
end krylov.Methods
