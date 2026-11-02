import krylov.Methods.OneGradientCoordinates
import krylov.Methods.WindowCoordinates

/-!
Article: main_krylov, alg:xrfc and lem:U(d), actual virtual-solve finite coordinates.
Use: identify genuine virtual corrections and extrapolated gradients with
fixed finite observed-vector arrays before differentiating any trial trajectory.
Source: actual model inverse reindexing and exact recorded-pair coordinates.
-/

namespace krylov.Methods
noncomputable section
open Matrix
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A true virtual window solve has its exact fixed-array physical correction and extrapolated gradient.
Use: actual XRFC regularity follows from true observed coefficient solves, including arbitrary incompatible pair data.
Article: main_krylov, alg:xrfc and lem:U(d).
Proof: actual list indices differ only by their pure dimension cast. The
true model matrix and inverse coefficients reindex together; collect the
physical correction and image combinations through the same finite equivalence. -/
theorem virtualWindow_coordinates (W : List (E × E)) {p : ℕ} (h : W.length=p)
    (S Y : Fin p → E) (hs : windowSteps W=S ∘ finCongr h) (hy : windowImages W=Y ∘ finCongr h)
    (g : E) :
    virtualCorrection W g=combine S (modelCoefficients S (pairModel S Y) g) ∧
    virtualGradient W g=g+combine Y (modelCoefficients S (pairModel S Y) g) := by
  -- Both real combinations use the same actual coefficient vector and the same genuine dimension cast.
  have hm := windowModel_of_coordinates W h S Y hs hy
  have hw : modelCoefficients (windowSteps W) (windowModel W) g=
      (modelCoefficients S (pairModel S Y) g) ∘ finCongr h := by
    rw [hs,hm]
    exact funext fun i => modelCoefficients_reindex (finCongr h) S (pairModel S Y) g i
  constructor
  · rw [virtualCorrection,virtualCoefficients,hw,hs]
    exact Equiv.sum_comp (finCongr h) (fun i => modelCoefficients S (pairModel S Y) g i • S i)
  · rw [virtualGradient,virtualCoefficients,hw,hy]
    congr 1
    exact Equiv.sum_comp (finCongr h) (fun i => modelCoefficients S (pairModel S Y) g i • Y i)

/-- Every actual full-memory one-gradient window retains its complete true segment-operator pair transcript.
Use: shared finite-coordinate direction and virtual solves read the same real observations.
Article: main_krylov, alg:xrfc and lem:U(d).
Proof: actual pair and record lengths agree, so full memory retains every genuinely recorded pair. -/
theorem oneGradient_full_window (m : OneGradientMethod E) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    selectedWindow fullMemory (oneGradientRun m A g k)=
      executedPairs (oneGradientStep m A g) (fun j => A j (oneGradientStep m A g j)) k := by
  change (oneGradientRun m A g k).pairs.take (oneGradientRun m A g k).records.length=_
  rw [oneGradientRun_length,oneGradientRun_pairs_segmentOperators,List.take_of_length_le (by rw [executedPairs_length])]

/-- The true full-memory observed conjugacy solve has its exact fixed finite one-gradient data formula for every supplied gradient.
Use: smooth XRFC directions are differentiated at the actual extrapolated gradient.
Article: main_krylov, alg:xrfc and lem:U(d).
Proof: substitute the real full pair transcript and the proved exact chronological direction reindexing identity. -/
theorem oneGradient_full_direction_coordinates (m : OneGradientMethod E)
    (A : ℕ → E →L[ℝ] E) (g v : E) (k : ℕ) :
    windowDirection (selectedWindow fullMemory (oneGradientRun m A g k)) v=
      conjugacyDirection (fun i : Fin k => oneGradientStep m A g (k-1-i.val))
        (fun i : Fin k => A (k-1-i.val) (oneGradientStep m A g (k-1-i.val))) v := by
  rw [oneGradient_full_window,windowDirection_executed]

/-- Every actual full-memory one-gradient window has its exact finite virtual correction and extrapolated gradient formulas.
Use: applies true finite C^r model calculus to real full-memory XRFC executions.
Article: main_krylov, alg:xrfc and lem:U(d).
Proof: the real full window retains the complete true pair transcript; its
proved newest-age coordinates supply both vector families to the genuine
virtual-window reindexing theorem. -/
theorem oneGradient_full_virtual_coordinates (m : OneGradientMethod E)
    (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    let H := oneGradientRun m A g k
    let S := fun i : Fin k => oneGradientStep m A g (k-1-i.val)
    let Y := fun i : Fin k => A (k-1-i.val) (oneGradientStep m A g (k-1-i.val))
    virtualCorrection (selectedWindow fullMemory H) H.gradient=combine S (modelCoefficients S (pairModel S Y) H.gradient) ∧
      virtualGradient (selectedWindow fullMemory H) H.gradient=H.gradient+combine Y (modelCoefficients S (pairModel S Y) H.gradient) := by
  -- The fixed coordinate length k comes from the actual number of evaluated records.
  have hw := oneGradient_full_window m A g k
  let W := executedPairs (oneGradientStep m A g) (fun j => A j (oneGradientStep m A g j)) k
  have hlen : W.length=k := executedPairs_length _ _ k
  let S := fun i : Fin k => oneGradientStep m A g (k-1-i.val)
  let Y := fun i : Fin k => A (k-1-i.val) (oneGradientStep m A g (k-1-i.val))
  have hs : windowSteps W=S ∘ finCongr hlen := by
    funext i
    exact congrArg Prod.fst (executedPairs_get _ _ k i.val (by simpa only [W,executedPairs_length] using i.isLt))
  have hy : windowImages W=Y ∘ finCongr hlen := by
    funext i
    exact congrArg Prod.snd (executedPairs_get _ _ k i.val (by simpa only [W,executedPairs_length] using i.isLt))
  dsimp only
  rw [hw]
  exact virtualWindow_coordinates W hlen S Y hs hy (oneGradientRun m A g k).gradient

end
end krylov.Methods
