import krylov.Methods.FC
import krylov.Secant.Residual

/-!
Article: main_krylov, alg:fc, lem:transfer and thm:A, actual FC trajectories.
Use: derive line orthogonality and retained conjugacy from the executed
data-only FC solve, then instantiate the exact residual staircase.
Source: exact FC equations; no differentiability or reference closeness is assumed.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual FC history on the prescribed segment-operator sequence.
Use: all trajectory quantities are projections of a genuine policy execution.
Article: main_krylov, alg:fc. -/
def fcHistory (memory : ℕ → ℕ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : History E :=
  methodRun (fcMethod memory) A A g k

/-- The actual observed gradient of the executed FC policy.
Use: exact transfer concerns the true adaptive trajectory.
Article: main_krylov, alg:fc, g_k. -/
def fcGradient (memory : ℕ → ℕ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  (fcHistory memory A g k).gradient

/-- The direction chosen by the executed data-only FC solve.
Use: derive its conjugacy from its actual coefficient inverse.
Article: main_krylov, alg:fc, d_k. -/
def fcDirection (memory : ℕ → ℕ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  (fcMethod memory).direction (fcHistory memory A g k)

/-- The exact-search displacement actually executed by FC.
Use: no hypothetical perturbed steps replace the real algorithmic update.
Article: main_krylov, alg:fc, s_k=α_kd_k. -/
def fcStep (memory : ℕ → ℕ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  lineLength (fcGradient memory A g k) (fcDirection memory A g k)
    (A k (fcDirection memory A g k)) • fcDirection memory A g k

/-- The actual observed FC secant through its actual segment operator.
Use: varying operators enter exact transfer through their real observations.
Article: main_krylov, alg:fc, y_k=A_ks_k. -/
def fcSecant (memory : ℕ → ℕ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E := A k (fcStep memory A g k)

/-- The executed FC gradient satisfies the exact prescribed secant update.
Use: verifies the trajectory hypothesis of the existing transfer theorem.
Article: main_krylov, lem:transfer, g_(k+1)=g_k+y_k.
Proof: execute the empty correction tree and move the actual line scalar through its actual segment operator. -/
theorem fcGradient_succ (memory : ℕ → ℕ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    fcGradient memory A g (k+1)=fcGradient memory A g k+fcSecant memory A g k := by
  change searchedGradient _ _ _=_
  simp only [searchedGradient, fcSecant, fcStep, map_smul]
  rfl

/-- The newest-first list of actually executed step/secant pairs.
Use: actual adaptive FC histories have explicit chronological indexing.
Article: main_krylov, alg:fc, observed pair transcript. -/
def executedPairs (s y : ℕ → E) : ℕ → List (E × E)
  | 0 => []
  | k+1 => (s k,y k)::executedPairs s y k

/-- The complete actual FC history contains exactly its executed step/secant pairs.
Use: retained conjugacy concerns the real observed entries supplied to the solver.
Article: main_krylov, alg:fc, record actual pairs.
Proof: induct over the executed history and apply its proved observed gradient update. -/
theorem fcHistory_pairs (memory : ℕ → ℕ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    (fcHistory memory A g k).pairs=executedPairs (fcStep memory A g) (fcSecant memory A g) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ((fcStep memory A g k+0,fcGradient memory A g (k+1)-fcGradient memory A g k)::
      (fcHistory memory A g k).pairs)=_
    rw [add_zero, fcGradient_succ, add_sub_cancel_left, ih]
    rfl

omit [InnerProductSpace ℝ E] [NormedAddCommGroup E] in
/-- The actual pair transcript has one entry per executed step.
Use: full retention keeps every executed pair.
Article: main_krylov, alg:fc, full window length.
Proof: each executed step prepends exactly one pair. -/
theorem executedPairs_length (s y : ℕ → E) (k : ℕ) : (executedPairs s y k).length=k := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [executedPairs, List.length_cons] using congrArg Nat.succ ih

omit [InnerProductSpace ℝ E] [NormedAddCommGroup E] in
/-- Every earlier actual pair belongs to the complete executed transcript.
Use: full-memory conjugacy includes every earlier observed image.
Article: main_krylov, lem:transfer, full retention.
Proof: the newest pair is the head and older pairs persist in the recursive transcript. -/
theorem executedPairs_contains (s y : ℕ → E) {i k : ℕ} (hi : i<k) : (s i,y i)∈executedPairs s y k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases he : i=k
    · subst i; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih (by omega))

/-- The actual full-memory FC window is exactly its complete executed pair transcript.
Use: discharges retention through the real selected-window implementation.
Article: main_krylov, lem:transfer, full conjugacy.
Proof: the actual pair length equals the actual iteration count, so full retention discards nothing. -/
theorem fullFC_window (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    selectedWindow fullMemory (fcHistory fullMemory A g k)=
      executedPairs (fcStep fullMemory A g) (fcSecant fullMemory A g) k := by
  have hl : (fcHistory fullMemory A g k).records.length=k := by
    rw [← History.pairs_length, fcHistory_pairs, executedPairs_length]
  change ((fcHistory fullMemory A g k).pairs).take (fcHistory fullMemory A g k).records.length=_
  rw [hl, fcHistory_pairs]
  exact List.take_of_length_le (by rw [executedPairs_length])

/-- Every actual nonzero-curvature FC search is orthogonal to its actual post-search gradient.
Use: derives the exact search condition from the executed line formula.
Article: main_krylov, lem:transfer and thm:A.
Proof: substitute the real line scalar and cancel its nonzero actual curvature. -/
theorem fcStep_line_orth (memory : ℕ → ℕ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ)
    (hc : inner ℝ (fcDirection memory A g k) (A k (fcDirection memory A g k))≠0) :
    inner ℝ (fcStep memory A g k) (fcGradient memory A g (k+1))=0 := by
  rw [fcGradient_succ]
  simp only [fcStep, fcSecant, map_smul, real_inner_smul_left, inner_add_right, real_inner_smul_right]
  rw [lineLength, div_mul_cancel₀ _ hc]
  ring

/-- Actual full-memory FC steps annihilate every earlier actual image when the actual solve is nonsingular.
Use: exact staircase conjugacy follows from the implemented inverse on the real adaptive history.
Article: main_krylov, lem:transfer and thm:A.
Proof: locate the old pair in the actual window, take its coordinate in the
computed conjugacy equation, and multiply by the executed line scalar. -/
theorem fullFC_step_conjugate (A : ℕ → E →L[ℝ] E) (g : E) {i k : ℕ} (hi : i<k)
    (hC : IsUnit (crossGram (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g k)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g k)))).det) :
    inner ℝ (fcStep fullMemory A g k) (fcSecant fullMemory A g i)=0 := by
  -- Locate the real old pair in the exact list supplied to the actual coefficient solve.
  let W := selectedWindow fullMemory (fcHistory fullMemory A g k)
  have hp : (fcStep fullMemory A g i,fcSecant fullMemory A g i)∈W := by
    rw [show W=executedPairs (fcStep fullMemory A g) (fcSecant fullMemory A g) k from fullFC_window A g k]
    exact executedPairs_contains _ _ hi
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hp
  have he := congrFun (conjugacyDirection_conjugate (windowSteps W) (windowImages W)
    (fcGradient fullMemory A g k) hC) j
  have hy : windowImages W j=fcSecant fullMemory A g i := congrArg Prod.snd hj
  change inner ℝ (windowImages W j) (fcDirection fullMemory A g k)=0 at he
  rw [hy, real_inner_comm] at he
  rw [fcStep, real_inner_smul_left, he, mul_zero]

variable {n : ℕ}

/-- The exact residual staircase for the actual executed full-memory FC policy.
Use: the real algorithmic starting point for differentiation and uniform remainder bounds.
Article: main_krylov, thm:A, exact staircase before differentiation.
Proof: actual execution supplies the secant recurrence, exact line pairing
and retained conjugacy; apply the existing exact transfer theorem in physical coordinates. -/
theorem fullFC_staircase (A : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (hsolve : ∀ k<N, IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g k)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g k)))).det)
    (hcurv : ∀ k<N, inner ℝ (fcDirection fullMemory A g k) (A k (fcDirection fullMemory A g k))≠0)
    {i : ℕ} (hi : i<N) :
    inner ℝ (fcStep fullMemory A g i) (fcGradient fullMemory A g N)=
      ∑ j∈Finset.Ico (i+1) N,
        (inner ℝ (fcStep fullMemory A g i) (fcSecant fullMemory A g j)-
          inner ℝ (fcStep fullMemory A g j) (fcSecant fullMemory A g i)) := by
  -- Transport actual Euclidean observations to the existing physical-coordinate staircase theorem.
  have hy := fun k => congrArg WithLp.ofLp (fcGradient_succ fullMemory A g k)
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm] using
    krylov.Secant.conjugate_staircase
      (fun k => WithLp.ofLp (fcGradient fullMemory A g k))
      (fun k => WithLp.ofLp (fcSecant fullMemory A g k))
      (fun k => WithLp.ofLp (fcStep fullMemory A g k)) hy hi
      (by simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm] using
        fcStep_line_orth fullMemory A g i (hcurv i hi))
      (fun j hj => by
        have hij : i<j := by have := Finset.mem_Ico.mp hj; omega
        simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm] using
          fullFC_step_conjugate A g hij (hsolve j (Finset.mem_Ico.mp hj).2))

end
end krylov.Methods
