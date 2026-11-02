import krylov.Methods.LaggedReplay
import krylov.Stability.ContDiffWindows
set_option autoImplicit false
/-!
Article: main_krylov, prop:hb, regularity of the actual lagged replay.
Use: derive smoothness from finite observed coordinates and genuine algebraic
domains, rather than assume regularity of the lagged policy or its trajectory.
Source: the chronological observed replay and the existing virtual block calculus.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The finite algebraic domain of the original chronological lagged cache.
Use: every condition concerns actual parent observations and actual computed
matrices; no regularity premise appears in this domain.
Article: main_krylov, prop:hb. -/
def laggedReplayDomain (directions : Bool) (tau0 : ℝ) (initial : E) :
    List (IterationRecord E) → Prop
  | [] => True
  | r::rs =>
    laggedReplayDomain directions tau0 initial rs ∧
      let H := History.mk initial rs
      let W := laggedWindow directions tau0 H
      let gv := virtualGradient W H.gradient
      let d := windowDirection W gv
      let q := (laggedTrial directions tau0 H)⁻¹ • (r.gradient-gv)
      (windowModel W).det≠0 ∧ (crossGram (windowImages W) (windowSteps W)).det≠0 ∧
        laggedTrial directions tau0 H≠0 ∧ inner ℝ d q≠0 ∧ 0<lineLength gv d q

omit [CompleteSpace E] in
/-- The true current observed gradient is smooth in smooth fixed record
coordinates, without a topology on histories.
Use: smooth replay induction reads exactly the real newest returned gradient.
Article: main_krylov, prop:hb and lem:U(d).
Proof: the empty transcript reads its initial observation; a nonempty one
reads its actual newest record. -/
theorem contDiff_recordGradient {r : WithTop ℕ∞} (initial : X → E)
    (records : List (X → IterationRecord E)) (x : X) (hi : ContDiffAt ℝ r initial x)
    (hg : ∀ f∈records,ContDiffAt ℝ r (fun z => (f z).gradient) x) :
    ContDiffAt ℝ r (fun z => (History.mk (initial z) (records.map (fun f => f z))).gradient) x := by
  cases records with
  | nil => exact hi
  | cons f fs => exact hg f (List.mem_cons_self)

omit [CompleteSpace E] in
/-- Every actual observed secant getter is smooth in the fixed smooth step
and returned-gradient records, including its genuine zero default.
Use: step-basis lagged replay uses real gradient differences.
Article: main_krylov, prop:hb and lem:U(d).
Proof: remove the newest real pair; its image is the difference of two
smooth genuine observations and every older getter is the parent getter. -/
theorem contDiff_recordPairs {r : WithTop ℕ∞} (initial : X → E)
    (records : List (X → IterationRecord E)) (x : X) (hi : ContDiffAt ℝ r initial x)
    (hs : ∀ f∈records,ContDiffAt ℝ r (fun z => (f z).step) x)
    (hg : ∀ f∈records,ContDiffAt ℝ r (fun z => (f z).gradient) x) (i : ℕ) :
    ContDiffAt ℝ r (fun z => ((recordPairs (initial z) (records.map (fun f => f z))).getD i (0,0)).1) x ∧
      ContDiffAt ℝ r (fun z => ((recordPairs (initial z) (records.map (fun f => f z))).getD i (0,0)).2) x := by
  induction records generalizing i with
  | nil => exact ⟨contDiffAt_const,contDiffAt_const⟩
  | cons f fs ih =>
    have hs' := fun f hf => hs f (List.mem_cons_of_mem _ hf)
    have hg' := fun f hf => hg f (List.mem_cons_of_mem _ hf)
    cases i with
    | zero => exact ⟨hs f (List.mem_cons_self),
        (hg f (List.mem_cons_self)).sub (contDiff_recordGradient initial fs x hi hg')⟩
    | succ i => exact ih hs' hg' i

/-- The actual lagged cache and its next decision are C^r in smooth finite
observations on the genuine positive measured replay domain.
Use: regularity is proved for the implemented S/D chronological replay,
including its original inverse measured image and locally inactive fallback.
Article: main_krylov, prop:hb, smooth data-only lagged trial.
Proof: induct through the real parent transcript; fixed-window virtual solves,
the nonzero previous trial and nonzero measured curvature are smooth. Strict
positivity keeps the measured branch active on a neighborhood. -/
theorem contDiff_laggedReplay {r : WithTop ℕ∞} (directions : Bool) (tau0 : ℝ)
    (initial : X → E) (records : List (X → IterationRecord E)) (x : X)
    (hi : ContDiffAt ℝ r initial x)
    (hs : ∀ f∈records,ContDiffAt ℝ r (fun z => (f z).step) x)
    (hg : ∀ f∈records,ContDiffAt ℝ r (fun z => (f z).gradient) x)
    (hdomain : laggedReplayDomain directions tau0 (initial x) (records.map (fun f => f x))) :
    (∀ i : ℕ,
      ContDiffAt ℝ r (fun z => ((laggedReplay directions tau0 (initial z)
        (records.map (fun f => f z))).1.getD i (0,0)).1) x ∧
      ContDiffAt ℝ r (fun z => ((laggedReplay directions tau0 (initial z)
        (records.map (fun f => f z))).1.getD i (0,0)).2) x) ∧
      ContDiffAt ℝ r (fun z => (laggedReplay directions tau0 (initial z)
        (records.map (fun f => f z))).2) x := by
  induction records with
  | nil => exact ⟨fun _ => ⟨contDiffAt_const,contDiffAt_const⟩,contDiffAt_const⟩
  | cons f fs ih =>
    have hs' := fun f hf => hs f (List.mem_cons_of_mem _ hf)
    have hg' := fun f hf => hg f (List.mem_cons_of_mem _ hf)
    obtain ⟨hold,hm,hc,ht,hq,hpositive⟩ := hdomain
    obtain ⟨hcache,htau⟩ := ih hs' hg' hold
    let H := fun z => History.mk (initial z) (fs.map (fun f => f z))
    let W := fun z => laggedWindow directions tau0 (H z)
    have hlen (z : X) : (W z).length=fs.length := by
      cases directions
      · exact (H z).pairs_length.trans (List.length_map _)
      · exact (lagged_replay_length true tau0 _ _).trans (List.length_map _)
    have hget (i : ℕ) :
        ContDiffAt ℝ r (fun z => ((W z).getD i (0,0)).1) x ∧
          ContDiffAt ℝ r (fun z => ((W z).getD i (0,0)).2) x := by
      cases directions
      · exact contDiff_recordPairs initial fs x hi hs' hg' i
      · exact hcache i
    have hblock := contDiff_windowBlock W hlen (fun z => (H z).gradient) x
      (fun i => (hget i.val).1) (fun i => (hget i.val).2)
      (contDiff_recordGradient initial fs x hi hg') hm hc
    let gv := fun z => virtualGradient (W z) (H z).gradient
    let d := fun z => windowDirection (W z) (gv z)
    let q := fun z => (laggedTrial directions tau0 (H z))⁻¹ • ((f z).gradient-gv z)
    have hqreg : ContDiffAt ℝ r q x :=
      (htau.inv ht).smul ((hg f (List.mem_cons_self)).sub hblock.2.1)
    let measured := fun z => lineLength (gv z) (d z) (q z)
    have hmeasured : ContDiffAt ℝ r measured x :=
      ((hblock.2.2.inner ℝ hblock.2.1).neg).div (hblock.2.2.inner ℝ hqreg) hq
    have hbranch : ContDiffAt ℝ r (fun z => if 0<measured z then measured z else tau0) x := by
      apply hmeasured.congr_of_eventuallyEq
      filter_upwards [hmeasured.continuousAt.eventually (isOpen_Ioi.mem_nhds hpositive)] with z hz
      exact ite_eq_left hz
    constructor
    · intro i
      cases i with
      | zero => exact ⟨hblock.2.2,hqreg⟩
      | succ i => exact hcache i
    · exact hbranch

end
end krylov.Stability
