import krylov.Stability.AnalyticCorrection
import krylov.Methods.WindowCoordinates
import krylov.Methods.ExecutedProbed

/-!
Article: main_krylov, lem:U(d), strict actual RFC observed-defect gates.
Use: prove an actual common local gate branch from genuine positive reference
pair energies, rather than assume a trajectory's branch is locally fixed.
Source: continuity of finite real inner products, square roots and the actual spectral matrix norm.
-/

namespace krylov.Stability
noncomputable section
open Matrix Filter krylov.Methods
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {b : ℕ}

omit [NormedSpace ℝ X] in
/-- The actual normalized observed-defect matrix is continuous at every positive-energy observation family.
Use: strict reference gate acceptance persists for the real nearby observed vectors.
Article: main_krylov, lem:U(d), continuity of the observed defect.
Proof: each genuine entry is a continuous inner-product difference divided
by a square root whose actual reference argument is a product of positive energies. -/
theorem pairDefect_continuousAt (s y : X → Fin b → E) (x : X)
    (hs : ∀ i, ContinuousAt (fun p => s p i) x) (hy : ∀ i, ContinuousAt (fun p => y p i) x)
    (he : ∀ i, 0 < inner ℝ (s x i) (y x i)) :
    ContinuousAt (fun p => pairDefect (s p) (y p)) x := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  exact ((hs i).inner (hy j) |>.sub ((hs j).inner (hy i))).div
    (((hs i).inner (hy i) |>.mul ((hs j).inner (hy j))).sqrt)
    (Real.sqrt_pos.mpr (mul_pos (he i) (he j))).ne'

/-- Genuine symmetric quadratic pair images have exactly zero actual normalized observed defect.
Use: every nonempty actual quadratic reference gate passes strictly.
Article: main_krylov, lem:U(d), strict quadratic observed gate.
Proof: the two real cross pairings agree by symmetry of the true quadratic operator. -/
theorem pairDefect_quadratic (s : Fin b → E) (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric) :
    pairDefect s (fun i => Q (s i))=0 := by
  ext i j
  have he := hQ (s j) (s i)
  change inner ℝ (Q (s j)) (s i)=inner ℝ (s j) (Q (s i)) at he
  simp only [pairDefect,← he,real_inner_comm (s i),sub_self,zero_div,Matrix.zero_apply]

omit [NormedSpace ℝ X] in
/-- True positive quadratic observations give a genuine neighborhood of strict RFC gate acceptance.
Use: all reference energies and the actual zero defect are discharged before choosing a local branch.
Article: main_krylov, lem:U(d), the gates pass strictly.
Proof: actual nonzero reference columns have positive true quadratic energies;
the actual defect norm is continuous and its actual reference value is zero. -/
theorem quadratic_pairDefect_gate (s y : X → Fin b → E) (x : X)
    (hs : ∀ i, ContinuousAt (fun p => s p i) x) (hy : ∀ i, ContinuousAt (fun p => y p i) x)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (hn : ∀ i, s x i≠0)
    (hyQ : ∀ i, y x i=Q (s x i)) :
    ∀ᶠ p in 𝓝 x, ‖pairDefect (s p) (y p)‖<1 := by
  -- This is a neighborhood theorem about the real observed gate, including its true spectral norm.
  have he : ∀ i, 0 < inner ℝ (s x i) (y x i) := by intro i; rw [hyQ]; exact hpos _ (hn i)
  have hc := (pairDefect_continuousAt s y x hs hy he).norm
  have hz : pairDefect (s x) (y x)=0 := by rw [funext hyQ]; exact pairDefect_quadratic _ Q hQ
  exact hc.eventually (Iio_mem_nhds (by
    change ‖pairDefect (s x) (y x)‖<1
    rw [hz,norm_zero]
    exact zero_lt_one))

omit [NormedSpace ℝ X] in
/-- Every genuine nonempty quadratic retained history has a common neighborhood of actual RFC gate acceptance.
Use: the strict local gate branch in actual prefix order estimates is discharged from real observed histories.
Article: main_krylov, lem:U(d), actual retained observed gate.
Proof: true chronological coordinates preserve the actual observed spectral
defect norm; the reference pair energies are positive and its genuine defect
is zero, while the nonempty retained length is fixed by the actual iteration count. -/
theorem retained_history_gate_eventually (memory : ℕ → ℕ) (H : X → History E)
    (s y : X → ℕ → E) (x : X) (k : ℕ)
    (hshape : ∀ p, (H p).pairs=executedPairs (s p) (y p) k)
    (hs : ∀ i<k, ContinuousAt (fun p => s p i) x)
    (hy : ∀ i<k, ContinuousAt (fun p => y p i) x)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hn : ∀ i : Fin (min (memory k) k), s x (k-1-i.val)≠0)
    (hyQ : ∀ i : Fin (min (memory k) k), y x (k-1-i.val)=Q (s x (k-1-i.val)))
    (hlen : min (memory k) k≠0) :
    ∀ᶠ p in 𝓝 x, selectedWindow memory (H p)≠[] ∧ ‖windowDefect (selectedWindow memory (H p))‖<1 := by
  -- The actual retained coordinate length is fixed even though its real observed vectors vary with the parameters.
  let S := fun p (i : Fin (min (memory k) k)) => s p (k-1-i.val)
  let Y := fun p (i : Fin (min (memory k) k)) => y p (k-1-i.val)
  have hS (i : Fin (min (memory k) k)) : ContinuousAt (fun p => S p i) x := by
    have hi := i.isLt
    exact hs _ (by omega)
  have hY (i : Fin (min (memory k) k)) : ContinuousAt (fun p => Y p i) x := by
    have hi := i.isLt
    exact hy _ (by omega)
  have hgate := quadratic_pairDefect_gate S Y x hS hY Q hQ hpos hn hyQ
  filter_upwards [hgate] with p hp
  have hW := selectedWindow_of_executed_pairs memory (H p) (s p) (y p) k (hshape p)
  have hne : selectedWindow memory (H p)≠[] := by
    intro hz
    have hl := congrArg List.length hz
    rw [hW,List.length_take,executedPairs_length,List.length_nil] at hl
    exact hlen hl
  refine ⟨hne,?_⟩
  rw [hW]
  have hc := retainedWindow_coordinates (s p) (y p) k (memory k)
  rw [windowDefect_norm_of_coordinates _ _ _ _ hc.1 hc.2]
  exact hp

end
end krylov.Stability
