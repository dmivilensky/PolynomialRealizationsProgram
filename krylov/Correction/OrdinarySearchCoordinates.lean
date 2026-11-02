import krylov.Correction.CycleData
import krylov.Stability.ObservedCanonical

/-!
Article: main_krylov, thm:UCq, actual ordinary search coordinates.
Use: Derive the real canonical line, searched gradient and conjugacy equations
needed by the terminal measured-response estimate from the original executor.
Source: the existing true positive-root pairing and operator covariance,
actual exact-search orthogonality and genuine observed chronological solves.
-/

namespace krylov.Correction
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual full retained defect norm is exactly the genuine finite measured-pair defect norm in newest-age coordinates.
Use: Read the original accepted ordinary-RFC gate in the exact terminal executor dictionary.
Article: main_krylov, thm:UCq.
Proof: The true executed-pair transcript fixes the actual retained length and entries. Apply the existing finite coordinate identity and eliminate the genuine full-memory minimum.
-/
theorem full_probed_defect_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    ‖windowDefect (selectedWindow fullMemory (methodRun m A B g k))‖=
      ‖pairDefect (fun i : Fin k => probedStep m A B g (k-1-i.val))
        (fun i : Fin k => probedSecant m A B g (k-1-i.val))‖ := by
  let s := probedStep m A B g
  let y := probedSecant m A B g
  let W := executedPairs s y k
  have hlen : W.length=k := executedPairs_length s y k
  have hs : windowSteps W=(fun i : Fin k => s (k-1-i.val)) ∘ finCongr hlen := by
    funext i
    exact congrArg Prod.fst (executedPairs_get s y k i.val (by simpa only [W,executedPairs_length] using i.isLt))
  have hy : windowImages W=(fun i : Fin k => y (k-1-i.val)) ∘ finCongr hlen := by
    funext i
    exact congrArg Prod.snd (executedPairs_get s y k i.val (by simpa only [W,executedPairs_length] using i.isLt))
  rw [fullWindow_methodRun]
  exact windowDefect_norm_of_coordinates W hlen _ _ hs hy

/-- The actual ordinary-RFC searched displacement has its exact canonical line-search representation.
Use: Compare the true original final search with its genuine CG reference.
Article: main_krylov, thm:UCq.
Proof: Actual primal/dual pairing preserves the real line scalar and the genuine probe operator transforms exactly through the positive metric root.
-/
theorem ordinary_canonical_line_step (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin n))
    let H := methodRun m A B g k
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    let D := R (m.direction H)
    lineLength (J H.gradient) D (canonicalOperator base (A k) D) • D=R (fullLineStep 1 A B g k) := by
  dsimp only
  rw [canonicalOperator_primal base hb,canonical_lineLength base hb]
  unfold fullLineStep
  dsimp only
  rw [map_smul]

/-- The actual ordinary-RFC searched gradient equals its true incoming canonical gradient plus the genuine canonical probe applied to its actual line displacement.
Use: Identify the actual vector in the terminal fresh-response calculation.
Article: main_krylov, thm:UCq.
Proof: Transform the real searched-gradient update through its genuine inverse metric root and use actual linearity and probe covariance.
-/
theorem ordinary_canonical_post_search (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    let m := rfcMethod fullMemory 1 (E := EuclideanSpace ℝ (Fin n))
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    J (fullPostSearch 1 A B g k)=J (probedGradient m A B g k)+
      canonicalOperator base (A k) (R (fullLineStep 1 A B g k)) := by
  dsimp only
  rw [canonicalOperator_primal base hb,fullPostSearch,fullLineStep]
  rw [searchedGradient,map_add]
  simp only [map_smul]
  rfl

/-- A genuinely defined ordinary-RFC search annihilates its real post-search gradient in the actual normalized canonical current-direction coordinate.
Use: Derive the zero last incoming-response coordinate even when the actual line scalar is zero.
Article: main_krylov, thm:UCq.
Proof: The true metric pairing is the physical direction/gradient pairing, which the existing exact searched-gradient identity makes zero on its actual nonzero-curvature domain.
-/
theorem ordinary_canonical_search_orthogonal (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hc : inner ℝ (probedDirection (rfcMethod fullMemory 1) A B g k)
      (A k (probedDirection (rfcMethod fullMemory 1) A B g k))≠0) :
    inner ℝ (NormedSpace.normalize (cgOperator (metricRoot base)
      (probedDirection (rfcMethod fullMemory 1) A B g k)))
      (cgOperator (metricRoot base)⁻¹ (fullPostSearch 1 A B g k))=0 := by
  rw [NormedSpace.normalize,real_inner_smul_left]
  have hp := canonical_search_pairing base hb
    (probedDirection (rfcMethod fullMemory 1) A B g k) (fullPostSearch 1 A B g k)
  change inner ℝ _ _=inner ℝ (cgOperator (metricRoot base) _) (cgOperator (metricRoot base)⁻¹ _) at hp
  rw [← hp]
  have hz := searchedGradient_inner_zero
    (probedGradient (rfcMethod fullMemory 1) A B g k)
    (probedDirection (rfcMethod fullMemory 1) A B g k)
    (A k (probedDirection (rfcMethod fullMemory 1) A B g k)) hc
  change inner ℝ (probedDirection (rfcMethod fullMemory 1) A B g k) (fullPostSearch 1 A B g k)=0 at hz
  rw [hz,mul_zero]

/-- The actual ordinary observed conjugacy inverse forces every true chronological canonical old secant to annihilate the real current search direction.
Use: Derive terminal fresh-response old-coordinate equations from the genuine measured solve.
Article: main_krylov, thm:UCq.
Proof: The true observed-list determinant is its genuine chronological determinant. Reuse the existing exact chronological canonical image-conjugacy theorem on those actual recorded pairs and identify the original full retained history.
-/
theorem ordinary_chronological_image_conjugacy (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (hC : IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (methodRun (rfcMethod fullMemory 1) A B g k)))
      (windowSteps (selectedWindow fullMemory (methodRun (rfcMethod fullMemory 1) A B g k)))).det)
    (i : Fin k) :
    inner ℝ (cgOperator (metricRoot base)⁻¹ (probedSecant (rfcMethod fullMemory 1) A B g i.val))
      (cgOperator (metricRoot base) (probedDirection (rfcMethod fullMemory 1) A B g k))=0 := by
  rw [full_probed_observed_solve_chronological] at hC
  have ht := chronological_canonical_image_conjugacy base hb
    (probedStep (rfcMethod fullMemory 1) A B g) (probedSecant (rfcMethod fullMemory 1) A B g)
    (probedGradient (rfcMethod fullMemory 1) A B g k) k hC i
  change inner ℝ (cgOperator (metricRoot base)⁻¹ (probedSecant (rfcMethod fullMemory 1) A B g i.val))
    (cgOperator (metricRoot base) (windowDirection
      (selectedWindow fullMemory (methodRun (rfcMethod fullMemory 1) A B g k))
      (probedGradient (rfcMethod fullMemory 1) A B g k)))=0
  rw [fullWindow_methodRun]
  exact ht

end
end krylov.Correction
