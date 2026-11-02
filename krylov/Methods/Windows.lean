import krylov.Methods.Protocol
import krylov.Methods.WindowConsistency
import krylov.Secant.Model

/-!
Article: main_krylov, def:methods and alg:fc, stored secant observations.
Use: derive actual pairs from the complete executed history and select only
the prescribed newest suffix. Lists store newest first; the model reverses
the index order so that it still retains the newer observation exactly.
Source: the source article's full, restarted and sliding pair-retention rules.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference Matrix
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual step/secant pairs extracted from observed iteration records, newest first.
Use: every model image is the difference of two genuinely observed gradients.
Article: main_krylov, alg:fc, append (s,g₊−g). -/
def recordPairs (initial : E) : List (IterationRecord E) → List (E × E)
  | [] => []
  | r::rs => (r.step, r.gradient-(History.mk initial rs).gradient)::recordPairs initial rs

/-- The actual secant pairs carried by the complete observed history.
Use: concrete policies read data rather than hidden operator actions.
Article: main_krylov, def:classes and alg:fc, observed secant window. -/
def History.pairs (H : History E) : List (E × E) := recordPairs H.initial H.records

omit [InnerProductSpace ℝ E] in
/-- Extracting actual secant pairs preserves the actual iteration count.
Use: finite history length determines the pair-retention rule without an external clock.
Article: main_krylov, alg:fc, iteration indexing.
Proof: each real iteration contributes exactly one recorded pair. -/
theorem History.pairs_length (H : History E) : H.pairs.length=H.records.length := by
  rcases H with ⟨initial, records⟩
  induction records with
  | nil => rfl
  | cons r rs ih => simpa only [History.pairs, recordPairs, List.length_cons] using congrArg Nat.succ ih

/-- The physical stored steps of a finite newest-first pair list.
Use: all finite coefficient solves use precisely this actual stored family.
Article: main_krylov, def:methods, S or D. -/
def windowSteps (W : List (E × E)) (i : Fin W.length) : E := (W.get i).1

/-- The physical stored images of a finite newest-first pair list.
Use: each image is observed, not recomputed with an unknown operator.
Article: main_krylov, def:methods, Y or Q. -/
def windowImages (W : List (E × E)) (i : Fin W.length) : E := (W.get i).2

/-- The latest-information model in the actual newest-first storage order.
Use: its current-probe row and old-window block are the exact algorithmic correction model.
Article: main_krylov, def:latest and alg:fc, H and T̄.
Source: Burdakov83; this reverses only the storage indexing of the existing latest model. -/
def windowModel (W : List (E × E)) : Matrix (Fin W.length) (Fin W.length) ℝ :=
  fun i j => inner ℝ (windowSteps W (max i j)) (windowImages W (min i j))

/-- The actual stored model is symmetric in either storage order.
Use: corrections solve a genuine symmetric model also for incompatible observed pairs.
Article: main_krylov, def:latest.
Proof: swapping the indices preserves their minimum and maximum. -/
theorem windowModel_symmetric (W : List (E × E)) : (windowModel W).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [windowModel, max_comm j i, min_comm j i]

/-- On genuine quadratic observations the stored latest model equals the actual positive operator Gram matrix.
Use: connects the implemented newest-first model to the proved generic quadratic solve.
Article: main_krylov, lem:consistent, H=UᵀAU.
Proof: the true symmetric operator makes each old/new pairing interchangeable. -/
theorem windowModel_quadratic (W : List (E × E)) (Q : E →L[ℝ] E)
    (hQ : Q.toLinearMap.IsSymmetric) (hy : ∀ i, windowImages W i=Q (windowSteps W i)) :
    windowModel W=crossGram (fun i => Q (windowSteps W i)) (windowSteps W) := by
  ext i j
  rcases le_total i j with hij | hji
  · simp only [windowModel, max_eq_right hij, min_eq_left hij, hy, crossGram]
    exact real_inner_comm _ _
  · simp only [windowModel, max_eq_left hji, min_eq_right hji, hy, crossGram]
    exact hQ _ _ |>.symm

/-- Select the actual suffix of pairs allowed at this iteration.
Use: the complete semantic transcript does not give the concrete method access to discarded pairs.
Article: main_krylov, def:methods, prescribed retention. -/
def selectedWindow (memory : ℕ → ℕ) (H : History E) : List (E × E) :=
  H.pairs.take (memory H.records.length)

/-- Full-memory retention keeps every previously recorded pair.
Use: full-cycle FC/RFC and the full-memory step-basis XRFC realization.
Article: main_krylov, alg:fc, full memory. -/
def fullMemory (k : ℕ) : ℕ := k

/-- A sliding window retains at most the prescribed number of newest pairs.
Use: every positive window length is represented by the same actual policy constructor.
Article: main_krylov, lem:consistent(a,c), memory m≥1. -/
def slidingMemory (m : ℕ) (_ : ℕ) : ℕ := m

/-- Restarted retention clears the stored window at each complete cycle boundary.
Use: source restarts occur after n actual reference iterations, not after an arbitrary shorter prefix.
Article: main_krylov, lem:consistent(a), restart every n iterations. -/
def restartedMemory (cycle k : ℕ) : ℕ := k%cycle

/-- A positive sliding window always retains the newest available pair.
Use: discharge the concrete memory hypothesis in all quadratic sliding consistency theorems.
Article: main_krylov, lem:consistent(a,c).
Proof: the retained count is the prescribed positive window length. -/
theorem slidingMemory_pos {m : ℕ} (hm : 0<m) (k : ℕ) : 0<slidingMemory m k := hm

/-- A full memory window retains the newest pair before every positive iteration.
Use: instantiate the common retained-window consistency theorem.
Article: main_krylov, lem:consistent(a,b).
Proof: the retained count equals the actual iteration count. -/
theorem fullMemory_pos {k : ℕ} (hk : 0<k) : 0<fullMemory k := hk

/-- Restarting after the complete cycle keeps every pair of its nonterminal prefix.
Use: the restart rule has exactly the source's full-cycle quadratic reference behavior.
Article: main_krylov, lem:consistent(a).
Proof: before the first cycle boundary the remainder is the actual iteration count. -/
theorem restartedMemory_prefix {cycle k : ℕ} (hk : k<cycle) : restartedMemory cycle k=k :=
  Nat.mod_eq_of_lt hk

/-- The actual complete reference pair transcript, newest first.
Use: the concrete FC/RFC policy invariant records observed pairs, not an assumed orthogonal state.
Article: main_krylov, lem:consistent, reference quadratic transcript. -/
def referencePairs (Q : E →L[ℝ] E) (g : E) : ℕ → List (E × E)
  | 0 => []
  | k+1 => (referenceStep Q g k, Q (referenceStep Q g k))::referencePairs Q g k

/-- The actual reference transcript contains one pair per executed iteration.
Use: compute concrete selected-window sizes in the consistency induction.
Article: main_krylov, lem:consistent.
Proof: induction on the actual finite transcript recursion. -/
theorem referencePairs_length (Q : E →L[ℝ] E) (g : E) (k : ℕ) : (referencePairs Q g k).length=k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [referencePairs, List.length_cons, ih]

/-- A stored reference pair at age i is the genuinely executed step at time k−1−i.
Use: selects arbitrary newest suffixes with an explicit injective chronological index map.
Article: main_krylov, lem:consistent, old-step indexing.
Proof: induction removes the newest pair and shifts the age of every older actual observation. -/
theorem referencePairs_get (Q : E →L[ℝ] E) (g : E) (k i : ℕ) (hi : i<k) :
    (referencePairs Q g k)[i]'(by rw [referencePairs_length]; exact hi)=
      (referenceStep Q g (k-1-i), Q (referenceStep Q g (k-1-i))) := by
  -- Removing the newest actual pair increases the stored age by exactly one.
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    cases i with
    | zero => simp only [referencePairs, List.getElem_cons_zero, Nat.add_sub_cancel, Nat.sub_zero]
    | succ i =>
      have hi' : i<k := by omega
      simpa only [referencePairs, List.getElem_cons_succ, Nat.add_sub_cancel,
        show k-(i+1)=k-1-i by omega] using ih i hi'

end
end krylov.Methods
