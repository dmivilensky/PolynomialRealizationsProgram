import krylov.Methods.OneGradient
import krylov.Methods.ExecutedFC

/-!
Article: main_krylov, def:classes(M₁) and lem:U(d), true finite observation charts.
Use: represent actual one-gradient histories by fixed finite vector coordinates
so that smooth data-only trial rules are hypotheses on primitive observed data.
Source: the actual one-gradient executor and chronological recorded-vector indexing.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- A finite observed vector tuple represents a genuine one-gradient history with newest observations first.
Use: C² trial rules are functions on these fixed observed coordinates, independently of any unknown operator.
Article: main_krylov, def:classes(M₁) and lem:U(d). -/
def oneGradientHistoryChart {k : ℕ} (data : E × (Fin k → E) × (Fin k → E)) : History E :=
  ⟨data.1,List.ofFn (fun i=>⟨0,0,data.2.1 i,data.2.2 i,[]⟩)⟩
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- A true chronological pair transcript has its exact fixed finite newest-age vector coordinates.
Use: finite smoothness charts represent actual retained histories without putting a fictitious norm on lists.
Article: main_krylov, lem:U(d).
Proof: remove the real newest pair and shift the true finite ages in the remaining actual prefix. -/
theorem executedPairs_ofFn (s y : ℕ → E) (k : ℕ) :
    executedPairs s y k=List.ofFn (fun i : Fin k=>(s (k-1-i.val),y (k-1-i.val))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [executedPairs,List.ofFn_succ,ih]
    congr 1
    congr 1
    funext i
    congr 1 <;> congr 1 <;> simp only [Fin.val_succ] <;> omega
/-- The actual evaluated displacement chosen from a real one-gradient history.
Use: coordinate charts include true query vectors rather than prescribed hypothetical steps.
Article: main_krylov, def:classes(M₁). -/
def oneGradientStep (m : OneGradientMethod E) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  m.step (oneGradientRun m A g k)
/-- The genuine gradient returned by the actual one-gradient execution.
Use: trial charts contain precisely the actual observed gradients.
Article: main_krylov, def:classes(M₁). -/
def oneGradientGradient (m : OneGradientMethod E) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  (oneGradientRun m A g k).gradient
/-- Every actual one-gradient history retains its genuine initial observation.
Use: the finite trial chart uses the same original gradient as the real executor.
Article: main_krylov, def:classes(M₁).
Proof: each actual evaluated update preserves the initial field. -/
theorem oneGradientRun_initial (m : OneGradientMethod E) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    (oneGradientRun m A g k).initial=g := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih
/-- The true one-gradient record list contains exactly the real queried steps and returned gradients.
Use: no hidden direction/probe slots enter the primitive observed trial chart.
Article: main_krylov, def:classes(M₁) and lem:U(d).
Proof: execute one real query and prepend precisely its actual step and actual returned gradient. -/
theorem oneGradientRun_records (m : OneGradientMethod E) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    (oneGradientRun m A g k).records=
      (executedPairs (oneGradientStep m A g) (fun j=>oneGradientGradient m A g (j+1)) k).map
        (fun p=>⟨0,0,p.1,p.2,[]⟩) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change ⟨0,0,oneGradientStep m A g k,oneGradientGradient m A g (k+1),[]⟩::
      (oneGradientRun m A g k).records=_
    rw [ih]
    rfl

/-- Every actual one-gradient history equals its fixed finite observed-data chart exactly.
Use: primitive C² trial-coordinate assumptions apply to the true executed policy, without assuming trial regularity along a desired trajectory.
Article: main_krylov, def:classes(M₁) and lem:U(d).
Proof: the actual initial observation is unchanged; the proved real record
transcript has the exact finite newest-age indexing, whose returned-gradient
index is one greater than its actual queried-step index. -/
theorem oneGradientRun_chart (m : OneGradientMethod E) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    oneGradientRun m A g k=oneGradientHistoryChart (g,
      (fun i : Fin k=>oneGradientStep m A g (k-1-i.val)),
      (fun i : Fin k=>oneGradientGradient m A g (k-i.val))) := by
  -- Identify the actual record list before comparing the full history structures.
  have hi := oneGradientRun_initial m A g k
  have hr : (oneGradientRun m A g k).records=(oneGradientHistoryChart (g,
      (fun i : Fin k=>oneGradientStep m A g (k-1-i.val)),
      (fun i : Fin k=>oneGradientGradient m A g (k-i.val)))).records := by
    change (oneGradientRun m A g k).records=List.ofFn _
    rw [oneGradientRun_records,executedPairs_ofFn,List.map_ofFn]
    congr 1
    funext i
    dsimp only [Function.comp_apply]
    have hi := i.isLt
    rw [show k-1-i.val+1=k-i.val by omega]
  cases h : oneGradientRun m A g k with
  | mk initial records =>
    simp only [h] at hi hr
    subst initial
    rw [hr]
    rfl

/-- Every actual one-gradient query returns its previous real gradient plus the actual segment-operator image of its real chosen step.
Use: all finite smoothness inductions propagate the genuine observed-gradient update.
Article: main_krylov, def:classes(M₁) and lem:U(d).
Proof: both sides unfold to the same actual one-gradient execution update. -/
theorem oneGradientGradient_succ (m : OneGradientMethod E) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    oneGradientGradient m A g (k+1)=oneGradientGradient m A g k+A k (oneGradientStep m A g k) := rfl

/-- The actual one-gradient pair transcript contains precisely its real evaluated steps and true segment-operator images.
Use: observed-coordinate model solves use actual secants even for varying segment operators.
Article: main_krylov, alg:xrfc and lem:U(d).
Proof: execute each real step, subtract its real previous gradient, and retain the earlier true transcript by induction. -/
theorem oneGradientRun_pairs_segmentOperators (m : OneGradientMethod E)
    (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    (oneGradientRun m A g k).pairs=executedPairs (oneGradientStep m A g)
      (fun j => A j (oneGradientStep m A g j)) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (oneGradientStep m A g k,oneGradientGradient m A g k+A k (oneGradientStep m A g k)-
      oneGradientGradient m A g k)::(oneGradientRun m A g k).pairs=_
    rw [add_sub_cancel_left,ih]
    rfl

/-- The actual physical displacement of a one-gradient prefix is the sum of its genuine evaluated queries.
Use: all point outputs inherit actual finite-step regularity without evaluating a virtual output.
Article: main_krylov, def:classes(M₁) and lem:U(d).
Proof: each actual executed record prepends its true chosen displacement;
the finite chronological sum has the same added newest term. -/
theorem oneGradientRun_displacement_sum (m : OneGradientMethod E)
    (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    (oneGradientRun m A g k).displacement=∑ i∈Finset.range k, oneGradientStep m A g i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change oneGradientStep m A g k+(oneGradientRun m A g k).displacement=_
    rw [ih,Finset.sum_range_succ,add_comm]

end
end krylov.Methods
