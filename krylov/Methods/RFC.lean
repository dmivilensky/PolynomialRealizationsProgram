import krylov.Methods.FC
import krylov.Methods.RepeatedCorrection
import Mathlib.Analysis.Matrix.Normed

/-!
Article: Definition 2.6 [def:methods] of krylov.tex.
Use: construct the gated repeated latest-information correction from observed
data and prove its quadratic consistency for every finite correction count.
Source: the source article's normalized observed-defect gate and RFC_k model.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual normalized observed skew defect of a stored pair window.
Use: the RFC gate inspects only observed pairings, with the true Euclidean operator norm.
Article: main_krylov, def:latest and alg:fc, δ. -/
def windowDefect (W : List (E × E)) : Matrix (Fin W.length) (Fin W.length) ℝ := fun i j =>
  (inner ℝ (windowSteps W i) (windowImages W j)-inner ℝ (windowSteps W j) (windowImages W i)) /
    Real.sqrt (inner ℝ (windowSteps W i) (windowImages W i)*
      inner ℝ (windowSteps W j) (windowImages W j))

/-- The actual repeated RFC correction rule, including its observed-defect gate.
Use: coefficients and every adaptive correction gradient depend only on observed data.
Article: main_krylov, alg:fc, nonempty window and ‖δ‖<1. -/
def rfcCorrection (memory : ℕ → ℕ) (count : ℕ) (H : History E) (z : E) : CorrectionTree E :=
  let W := selectedWindow memory H
  let d := windowDirection W H.gradient
  let U := (d,z)::W
  if W≠[] ∧ ‖windowDefect W‖<1 then
    repeatedModelTree (windowSteps U) (windowModel U) count (searchedGradient H.gradient d z)
  else .done

/-- The concrete repeated RFC policy with observed pair retention and a fixed finite correction count.
Use: RFC is count one; every RFC_k is an actual nonanticipating executed policy.
Article: main_krylov, def:methods and alg:fc. -/
def rfcMethod (memory : ℕ → ℕ) (count : ℕ) : ProbedMethod E :=
  retainedMethod memory (rfcCorrection memory count)

/-- Genuine quadratic pair data have exactly zero observed normalized skew defect.
Use: the actual RFC gate accepts every nonempty quadratic reference window.
Article: main_krylov, lem:consistent(a), observed symmetry.
Proof: true symmetry annihilates each numerator, without dividing by a possibly zero stopped-tail energy. -/
theorem windowDefect_quadratic (W : List (E × E)) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hy : ∀ i, windowImages W i=Q (windowSteps W i)) :
    windowDefect W=0 := by
  ext i j
  have he := hQ (windowSteps W j) (windowSteps W i)
  change inner ℝ (Q (windowSteps W j)) (windowSteps W i)=
    inner ℝ (windowSteps W j) (Q (windowSteps W i)) at he
  simp only [windowDefect, hy, ← he, real_inner_comm (windowSteps W i),
    sub_self, zero_div, Matrix.zero_apply]

/-- The actual RFC_k quadratic corrections vanish on every actual reference transcript.
Use: discharges the executed retained-method induction for the concrete gated policy.
Article: main_krylov, lem:consistent(a), zero corrections.
Proof: the gate either skips corrections or the actual augmented post-search
coordinates vanish; every computed repeated coefficient is then zero. -/
theorem rfcCorrection_reference (memory : ℕ → ℕ) (count : ℕ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) (H : History E)
    (hg : H.gradient=CG.gradient Q g k) (hp : H.pairs=referencePairs Q g k)
    (hm : CG.gradient Q g k≠0 → 0<k → 0<memory k) :
    ZeroCorrections (rfcCorrection memory count H (Q ((rfcMethod memory count).direction H))) Q
      (searchedGradient H.gradient ((rfcMethod memory count).direction H)
        (Q ((rfcMethod memory count).direction H))) := by
  -- Use the actual retained-window direction before reasoning about either branch of the observed-data gate.
  have hd := retainedMethod_direction memory (rfcCorrection memory count) Q hQ hpos g k H hg hp hm
  change windowDirection (selectedWindow memory H) H.gradient=CG.direction Q g k at hd
  have hl : H.records.length=k := by rw [← H.pairs_length, hp, referencePairs_length]
  change ZeroCorrections (rfcCorrection memory count H (Q (windowDirection _ _))) Q _
  unfold rfcCorrection
  dsimp only
  split
  · apply repeatedModelTree_zero
    rw [hd, hg]
    by_cases hz : CG.gradient Q g k=0
    · have hs : searchedGradient (CG.gradient Q g k) (CG.direction Q g k) (Q (CG.direction Q g k))=0 := by
        rw [hz, direction_zero_of_gradient Q g k hz]
        simp only [searchedGradient, map_zero, smul_zero, add_zero]
      rw [hs]
      ext i
      exact inner_zero_right _
    · change coordinates (windowSteps ((CG.direction Q g k,Q (CG.direction Q g k))::
        selectedWindow memory H)) (CG.gradient Q g (k+1))=0
      have hW : selectedWindow memory H=(referencePairs Q g k).take (memory k) := by
        unfold selectedWindow
        rw [hp, hl]
      rw [hW]
      exact reference_augmented_coordinates Q hQ hpos g k (memory k) hz
  · trivial

/-- Every concrete RFC_k run has exactly the actual CG gradients and recorded pairs on static quadratic data.
Use: the assertion covers all intermediate correction queries and every finite repeated-correction count.
Article: main_krylov, lem:consistent(a).
Proof: the actual computed RFC correction rule discharges the shared executed-policy induction. -/
theorem rfcMethod_static (memory : ℕ → ℕ) (count : ℕ)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E)
    (hm : ∀ k, CG.gradient Q g k≠0 → 0<k → 0<memory k) (k : ℕ) :
    let H := methodRun (rfcMethod memory count) (fun _ => Q) (fun _ => Q) g k
    H.gradient=CG.gradient Q g k ∧ H.pairs=referencePairs Q g k :=
  retainedMethod_static memory _ Q hQ hpos g hm
    (fun j H hg hp => rfcCorrection_reference memory count Q hQ hpos g j H hg hp (hm j)) k

/-- Concrete RFC_k is globally CG-consistent for every memory retaining the newest pair and every finite correction count.
Use: applies the exact data-fibre results to real full and sliding repeated RFC policies.
Article: main_krylov, lem:consistent(a).
Proof: actual reference transcripts give scale-one CG directions and the proved
actual zero correction trees, for every symmetric positive operator. -/
theorem rfcMethod_consistent (memory : ℕ → ℕ) (hm : ∀ k, 0<k → 0<memory k) (count : ℕ) :
    CGConsistent (rfcMethod memory count : ProbedMethod E) := by
  intro Q hQ hpos g k
  have hs := rfcMethod_static memory count Q hQ hpos g (fun k _ => hm k) k
  refine ⟨1, zero_lt_one, ?_, ?_⟩
  · change (retainedMethod memory _).direction _=1 • CG.direction Q g k
    rw [one_smul]
    exact retainedMethod_direction memory _ Q hQ hpos g k _ hs.1 hs.2 (fun _ => hm k)
  · exact rfcCorrection_reference memory count Q hQ hpos g k _ hs.1 hs.2 (fun _ => hm k)

end
end krylov.Methods
