import krylov.Methods.DirectionSolve

/-!
Article: main_krylov, alg:xrfc-D and lem:consistent(c), actual direction-basis data.
Use: implement XRFC-D without access to any unknown operator action; each
new direction image is recovered solely from its actual observed gradient.
Source: q_k=(g_(k+1)−ĝ_k)/τ_k in the source one-gradient protocol.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Reconstruct the actual newest-first direction-pair transcript solely from past observed records.
Use: directions and their images are data-only functions; no operator is available to this replay.
Article: main_krylov, alg:xrfc-D, q_k=(g_(k+1)−ĝ_k)/τ_k. -/
def directionReplay (memory : ℕ → ℕ) (trial : History E → ℝ) (initial : E) :
    List (IterationRecord E) → List (E × E)
  | [] => []
  | r::rs =>
    let H := History.mk initial rs
    let old := directionReplay memory trial initial rs
    let W := old.take (memory rs.length)
    let gv := virtualGradient W H.gradient
    (windowDirection W gv,(trial H)⁻¹ • (r.gradient-gv))::old

/-- Select the actual retained direction-pair window reconstructed from observed data.
Use: the XRFC-D coefficient solve receives precisely the retained replayed directions and observed images.
Article: main_krylov, alg:xrfc-D, D and Q. -/
def selectedDirectionWindow (memory : ℕ → ℕ) (trial : History E → ℝ) (H : History E) : List (E × E) :=
  (directionReplay memory trial H.initial H.records).take (memory H.records.length)

/-- The actual one-gradient XRFC-D policy with a data-only trial rule and direction-pair retention.
Use: arbitrary positive newest-retaining windows require only the actual one gradient query per iteration.
Article: main_krylov, alg:xrfc-D, virtual correction plus trial direction and unevaluated virtual output. -/
def xrfcDMethod (memory : ℕ → ℕ) (trial : History E → ℝ) : OneGradientMethod E where
  step H :=
    let W := selectedDirectionWindow memory trial H
    virtualCorrection W H.gradient+trial H • windowDirection W (virtualGradient W H.gradient)
  output H := virtualCorrection (selectedDirectionWindow memory trial H) H.gradient

/-- Replaying an actual new XRFC-D record appends its actual chosen direction and its gradient-difference image.
Use: quadratic replay correctness is proved from the real query rather than postulated stored pairs.
Article: main_krylov, lem:consistent(c), actual observed direction pairs.
Proof: unfold the actual query record and replay recursion at its newest record. -/
theorem directionReplay_advance (memory : ℕ → ℕ) (trial : History E → ℝ)
    (A : E →L[ℝ] E) (H : History E) :
    let m := xrfcDMethod memory trial
    let W := selectedDirectionWindow memory trial H
    directionReplay memory trial (oneGradientAdvance m A H).initial (oneGradientAdvance m A H).records=
      (windowDirection W (virtualGradient W H.gradient),
        (trial H)⁻¹ • (H.gradient+A (m.step H)-virtualGradient W H.gradient))::
          directionReplay memory trial H.initial H.records := rfl

end
end krylov.Methods
