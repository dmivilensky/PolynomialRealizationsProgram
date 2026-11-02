import krylov.Convergence.SecantWindowSource

/-!
Article: main_krylov, thm:Ip and thm:ss1F.
Use: actual sliding executions with an initial finite history. Every next
query is computed from earlier observed values and gradients. The execution
definition contains no convergence, error recurrence, or model-limit fields.
Source: the one-gradient multipoint secant rule (Burdakov83), and its
function-value diagonal correction in Appendix G.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Methods krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- Execute any specified finite sliding rule on its actual chronological
window. All recursive indices are strictly earlier queries. -/
def slidingSequence {E : Type*} (rule : (Fin (n+2) → E) → E)
    (seed : Fin (n+2) → E) (k : ℕ) : E :=
  if hk : k<n+2 then seed ⟨k,hk⟩ else
    rule (fun i=>slidingSequence rule seed (k-(n+2)+i.val))
termination_by k
decreasing_by omega

theorem slidingSequence_seed {E : Type*} (rule : (Fin (n+2) → E) → E)
    (seed : Fin (n+2) → E) (i : Fin (n+2)) : slidingSequence rule seed i.val=seed i := by
  rw [slidingSequence,dite_eq_left i.isLt]

/-- The actual next query uses exactly the last n+2 points, in order. -/
theorem slidingSequence_step {E : Type*} (rule : (Fin (n+2) → E) → E)
    (seed : Fin (n+2) → E) (k : ℕ) :
    slidingSequence rule seed (k+n+2)=rule (fun i=>slidingSequence rule seed (k+i.val)) := by
  rw [slidingSequence,dite_eq_right (by omega : ¬k+n+2<n+2)]
  congr 1
  funext i
  congr 1
  omega

/-- SS1's real sliding rule. The endpoint gradient is the only new gradient
of the preceding iteration; all other gradients are stored observations. -/
def ss1WindowRule {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : E → E) (q : Fin (n+2) → E) : E :=
  ss1Point (fun i : Fin (n+1)=>q i.succ-q i.castSucc)
    (fun i=>G (q i.succ)-G (q i.castSucc)) (G (q (Fin.last (n+1)))) (q (Fin.last (n+1)))

/-- The value-corrected sliding rule with an actual data-dependent split
policy. No inverse-model formula is supplied to the executor. -/
def ss1FWindowRule {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (G : E → E) (split : (Fin (n+2) → E) → Fin (n+1) → ℝ)
    (q : Fin (n+2) → E) : E :=
  ss1FPoint f G (fun i : Fin (n+1)=>q i.castSucc)
    (fun i=>q i.succ-q i.castSucc) (split q) (q (Fin.last (n+1)))

/-- The genuine SS1 iteration from its initial observed history. -/
def ss1Sequence {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : E → E) (seed : Fin (n+2) → E) : ℕ → E := slidingSequence (ss1WindowRule G) seed

/-- The genuine SS1-F iteration from its initial observed history. -/
def ss1FSequence {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (G : E → E) (split : (Fin (n+2) → E) → Fin (n+1) → ℝ)
    (seed : Fin (n+2) → E) : ℕ → E := slidingSequence (ss1FWindowRule f G split) seed

theorem ss1Sequence_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : E → E) (seed : Fin (n+2) → E) (k : ℕ) :
    ss1Sequence G seed (k+n+2)=ss1Point (windowStep (n:=n+1) (ss1Sequence G seed) k)
      (windowImage G (ss1Sequence G seed) k) (G (ss1Sequence G seed (k+n+1)))
      (ss1Sequence G seed (k+n+1)) := by
  rw [ss1Sequence,slidingSequence_step]
  rfl

theorem ss1FSequence_step {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (G : E → E) (split : (Fin (n+2) → E) → Fin (n+1) → ℝ)
    (seed : Fin (n+2) → E) (k : ℕ) :
    ss1FSequence f G split seed (k+n+2)=ss1FPoint f G
      (windowAnchor (n:=n+1) (ss1FSequence f G split seed) k)
      (windowStep (ss1FSequence f G split seed) k)
      (split (fun i=>ss1FSequence f G split seed (k+i.val)))
      (ss1FSequence f G split seed (k+n+1)) := by
  rw [ss1FSequence,slidingSequence_step]
  rfl

/-- Genuine convergent SS1 executions are superlinear under the original
uniform normalized-window independence hypothesis. -/
theorem ss1Sequence_superlinear
    (G : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (H : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n+1)))
    (S : Set (EuclideanSpace ℝ (Fin (n+1)))) (hS : Convex ℝ S)
    (h₀ : (0:EuclideanSpace ℝ (Fin (n+1)))∈S) (hnbhd : S∈𝓝 0)
    {L : ℝ≥0} (hH : LipschitzOnWith L H S) (hH₀ : H 0=ContinuousLinearMap.id ℝ _)
    (hG : ∀ z∈S, HasFDerivAt G (H z) z) (hG₀ : G 0=0)
    (seed : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)))
    (hconv : Tendsto (ss1Sequence G seed) atTop (𝓝 0))
    {σ : ℝ} (hσ : 0<σ)
    (hind : ∀ᶠ k in atTop,
      IsUnit (windowMatrix (unitWindow (windowStep (ss1Sequence G seed) k))).det ∧
      σ≤leastGain (windowMatrix (unitWindow (windowStep (ss1Sequence G seed) k)))) :
    (fun k=>ss1Sequence G seed (k+1)) =o[atTop] (fun k=>‖ss1Sequence G seed k‖) := by
  let x := ss1Sequence G seed
  have ha (i : Fin (n+1)) : Tendsto (fun k=>x (k+i.val)) atTop (𝓝 0) :=
    hconv.comp (tendsto_add_atTop_nat i.val)
  have hb (i : Fin (n+1)) : Tendsto (fun k=>x (k+i.val+1)) atTop (𝓝 0) := by
    simpa only [Nat.add_assoc,Function.comp_def,x] using hconv.comp (tendsto_add_atTop_nat (i.val+1))
  have hx : Tendsto (fun k=>x (k+n+1)) atTop (𝓝 0) := by
    simpa only [Nat.add_assoc,Function.comp_def,x] using hconv.comp (tendsto_add_atTop_nat (n+1))
  have hm : ∀ᶠ k in atTop,
      (∀ i : Fin (n+1),x (k+i.val)∈S) ∧
      (∀ i : Fin (n+1),x (k+i.val+1)∈S) ∧x (k+n+1)∈S :=
    ((Filter.eventually_all.mpr fun i=>(ha i).eventually hnbhd).and
      (Filter.eventually_all.mpr fun i=>(hb i).eventually hnbhd)).and
      (hx.eventually hnbhd) |>.mono fun _ h=>⟨h.1.1,h.1.2,h.2⟩
  have hi : ∀ᶠ k in atTop,
      IsUnit (windowMatrix (unitWindow (windowStep x k))).det ∧
      ‖(windowMatrix (unitWindow (windowStep x k)))⁻¹‖≤σ⁻¹ :=
    hind.mono fun k h=>⟨h.1,Secant.inverse_bound_of_leastGain _ h.1 hσ h.2⟩
  have hh := ss1_source_superlinear G H S hS h₀ hH hH₀ hG hG₀
    (fun k i=>x (k+i.val)) (fun k i=>x (k+i.val+1)) (fun k=>x (k+n+1))
    ha hb hx hm (inv_nonneg.mpr hσ.le) hi
  have hs : (fun k=>x (k+n+2)) =o[atTop] (fun k=>‖x (k+n+1)‖) :=
    hh.congr_left fun k=>(ss1Sequence_step G seed k).symm
  have hmap : ((fun k=>x (k+1)) ∘ (fun k=>k+(n+1))) =o[atTop]
      ((fun k=>‖x k‖) ∘ (fun k=>k+(n+1))) := by
    simpa only [Function.comp_def,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hs
  have hout := (Asymptotics.isLittleO_map).mpr hmap
  simpa only [Filter.map_add_atTop_eq_nat] using hout

end
end krylov.Convergence
