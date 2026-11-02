import krylov.Methods.XRFCBasisHistory
set_option autoImplicit false
/-!
Article: main_krylov, prop:hb, actual data-only lagged trials in both bases.
Use: reconstruct the previous measured exact length from genuine observed
gradients, using the actual selected basis and previously chosen trial.
Source: the original chronological XRFC replay and the source formula
q_(k-1)=(g_k-gHat_(k-1))/tau_(k-1); no unknown operator is supplied.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The original previous-step exact length reconstructed from observed data.
Use: the previous virtual direction and gradient are formed in the actual
stored basis, and its image uses only the newly returned real gradient.
Article: main_krylov, prop:hb. -/
def laggedMeasuredLength (W : List (E × E)) (g : E) (tau : ℝ) (next : E) : ℝ :=
  let gv := virtualGradient W g
  let d := windowDirection W gv
  lineLength gv d (tau⁻¹ • (next-gv))

/-- Actual chronological cache of observed direction images and next lagged
trial, in either original XRFC basis. A positive fallback totalizes histories
outside the genuine positive quadratic domain.
Use: recursion reads the true parent transcript and never queries an operator.
Article: main_krylov, prop:hb, lagged measured Rayleigh trial. -/
def laggedReplay (directions : Bool) (tau0 : ℝ) (initial : E) :
    List (IterationRecord E) → List (E × E) × ℝ
  | [] => ([],tau0)
  | r::rs =>
    let old := laggedReplay directions tau0 initial rs
    let H := History.mk initial rs
    let W := if directions then old.1 else H.pairs
    let gv := virtualGradient W H.gradient
    let d := windowDirection W gv
    let q := old.2⁻¹ • (r.gradient-gv)
    let t := lineLength gv d q
    ((d,q)::old.1,if 0<t then t else tau0)

/-- One genuine history-only lagged-trial rule for the selected XRFC basis.
Use: previous decisions are obtained by the same chronological cache, so the
actual direction replay has no circular or assumed trial input.
Article: main_krylov, prop:hb. -/
def laggedTrial (directions : Bool) (tau0 : ℝ) (H : History E) : ℝ :=
  (laggedReplay directions tau0 H.initial H.records).2

/-- The actual basis window used by the lagged measurement cache.
Use: distinguish stored steps from genuinely reconstructed direction pairs.
Article: main_krylov, prop:hb. -/
def laggedWindow (directions : Bool) (tau0 : ℝ) (H : History E) : List (E × E) :=
  if directions then (laggedReplay directions tau0 H.initial H.records).1 else H.pairs

/-- Every real recorded query contributes one cached direction/image pair.
Use: full direction retention has its actual native length, not an assumption.
Article: main_krylov, prop:hb.
Proof: induction over the genuine parent-record recursion. -/
theorem lagged_replay_length (directions : Bool) (tau0 : ℝ) (initial : E)
    (records : List (IterationRecord E)) : (laggedReplay directions tau0 initial records).1.length=records.length := by
  induction records with
  | nil => rfl
  | cons r rs ih => exact congrArg Nat.succ ih

/-- Positive initialization makes the actual lagged policy positive on every
history. At genuine active quadratic data its measured branch is used.
Use: all actual native basis and inverse domains follow without a trial premise.
Article: main_krylov, prop:hb.
Proof: a nonempty cache chooses a strictly positive measured value or tau0. -/
theorem lagged_trial_positive (directions : Bool) {tau0 : ℝ} (htau0 : 0<tau0) (H : History E) :
    0<laggedTrial directions tau0 H := by
  cases H with
  | mk initial records =>
    cases records with
    | nil => exact htau0
    | cons r rs =>
      unfold laggedTrial laggedReplay
      dsimp only
      split_ifs <;> assumption

/-- The original lagged cache is exactly the native XRFC-D direction replay
with that same actual lagged trial policy, on every observed history.
Use: the implementation is a real direction-basis policy also off quadratics.
Article: main_krylov, prop:hb, genuine XRFC-D implementation dictionary.
Proof: the two chronological recursions have the same true previous trial;
their complete old direction caches have exactly the actual record length. -/
theorem lagged_replay_direction (tau0 : ℝ) (initial : E) (records : List (IterationRecord E)) :
    (laggedReplay true tau0 initial records).1=
      directionReplay fullMemory (laggedTrial true tau0) initial records := by
  induction records with
  | nil => rfl
  | cons r rs ih =>
    rw [directionReplay,← ih]
    have htake : ((laggedReplay true tau0 initial rs).1).take (fullMemory rs.length)=
        (laggedReplay true tau0 initial rs).1 := by
      change ((laggedReplay true tau0 initial rs).1).take rs.length=_
      rw [← lagged_replay_length true tau0 initial rs,List.take_length]
    rw [htake]
    rfl

/-- The cache's selected step window is exactly the actual full step window.
Use: real observed trial measurements use the same pairs as native XRFC-S.
Article: main_krylov, prop:hb.
Proof: both are the actual complete observed step/secant transcript. -/
theorem lagged_window_step (tau0 : ℝ) (H : History E) :
    laggedWindow false tau0 H=selectedWindow fullMemory H := (selectedWindow_full H).symm

/-- The cache's selected direction window is exactly the native full replay
window for its genuine actual lagged policy.
Use: no step-basis replacement is made away from quadratic reference data.
Article: main_krylov, prop:hb.
Proof: the actual cache/native replay equality and their genuine length remove
the full-retention take operation. -/
theorem lagged_window_direction (tau0 : ℝ) (H : History E) :
    laggedWindow true tau0 H=selectedDirectionWindow fullMemory (laggedTrial true tau0) H := by
  rw [selectedDirectionWindow,← lagged_replay_direction]
  change (laggedReplay true tau0 H.initial H.records).1=
    ((laggedReplay true tau0 H.initial H.records).1).take H.records.length
  rw [← lagged_replay_length true tau0 H.initial H.records,List.take_length]

/-- After a real evaluated query, the lagged decision is precisely the
previous measured exact length, with a positive off-domain totalization.
Use: all actual reference and regularity proofs start from this original
observation formula, not a prescribed sequence of CG lengths.
Article: main_krylov, prop:hb.
Proof: unfold the single true new cache record and the parent decision. -/
theorem lagged_trial_advance (directions : Bool) (tau0 : ℝ) (method : OneGradientMethod E)
    (Q : E →L[ℝ] E) (H : History E) :
    laggedTrial directions tau0 (oneGradientAdvance method Q H)=
      let t := laggedMeasuredLength (laggedWindow directions tau0 H) H.gradient
        (laggedTrial directions tau0 H) (H.gradient+Q (method.step H))
      if 0<t then t else tau0 := by
  cases directions <;> rfl

end
end krylov.Methods
