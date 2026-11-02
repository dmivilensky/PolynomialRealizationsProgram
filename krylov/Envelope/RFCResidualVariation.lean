import krylov.Envelope.ResidualOrders
import krylov.Envelope.TiltSplitting
import krylov.Stability.RFCRecordedOrders

set_option autoImplicit false
/-!
Article: main_krylov, apB:eq:nu and thm:select, genuine full-memory RFC residual variation.
Use: derive the actual vanishing first variation of every true recorded
step-gradient residual from the previously proved complete executed RFC
projected-residual order, for every positive finite correction count.
Source: actual nondegenerate RFC execution and genuine recorded-window
orders, true zero-safe unnormalization and the real derivative criterion.
-/

namespace krylov.Envelope
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual full-memory RFC recorded-step/returned-gradient residual has genuine derivative zero after a noninitial positive-correction prefix.
Use: Every actual full-memory RFC recorded-step/returned-gradient residual has genuine derivative zero after a noninitial positive-correction prefix.
Article: main_krylov, apB:eq:nu and thm:select, genuine full-memory RFC residual variation.
Proof: Use the actual recorded-window residual order from the genuine RFC executor. Identify its true newest-first coordinates with every real chronological recorded step; locally bounded actual column norms transfer the proved superlinear order to each true observed residual, giving its real zero derivative. -/
theorem fullRFC_residual_zero_derivative (count : ℕ) (hc : 0<count)
    (A B : ℝ → ℕ → E →L[ℝ] E) (g : E)
    (hA : ∀ i, AnalyticAt ℝ (fun t => A t i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun t => B t i) 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (k : ℕ) (hk : 0<k) (hpre : ∀ i≤k, CG.gradient Q g i≠0) (i : ℕ) (hi : i≤k) :
    HasDerivAt (fun t => inner ℝ (probedStep (rfcMethod fullMemory count) (A t) (B t) g i)
      (probedGradient (rfcMethod fullMemory count) (A t) (B t) g (k+1))) 0 0 := by
  -- Use the genuine RFC executor and its actual full recorded window, preserving real chronological step indices.
  let m := rfcMethod fullMemory count (E := E)
  let V := fun t (j : Fin (k+1)) => probedStep m (A t) (B t) g (k-j.val)
  let G := fun t => probedGradient m (A t) (B t) g (k+1)
  have hm : ∀ j, CG.gradient Q g j≠0 → 0<j → 0<fullMemory j := fun _ _ hj => hj
  have hs := quadraticRFC_recorded_projected_order fullMemory count A B (fun _ => g) hA hB analyticAt_const
    Q hA0 hB0 hQ hpos hm k hk hpre
  have hs' : (fun t => projectedResidual (unitWindow
      (Fin.cons (probedStep m (A t) (B t) g k)
        (fun j : Fin k => probedStep m (A t) (B t) g (k-1-j.val)))) (G t)) =O[𝓝 (0 : ℝ)]
      (fun t => ‖t‖^(count+1)) := by
    dsimp only at hs
    rw [show min (fullMemory k) k=k from min_self k] at hs
    exact hs
  have hV (t : ℝ) : Fin.cons (probedStep m (A t) (B t) g k)
      (fun j : Fin k => probedStep m (A t) (B t) g (k-1-j.val))=V t := by
    funext j
    refine Fin.cases rfl (fun l => ?_) j
    change probedStep m (A t) (B t) g (k-1-l.val)=probedStep m (A t) (B t) g (k-(l.val+1))
    congr 1
    omega
  have hO : (fun t => projectedResidual (unitWindow (V t)) (G t)) =O[𝓝 (0 : ℝ)] (fun t => ‖t‖^(count+1)) :=
    hs'.congr_left fun t => by rw [hV]
  have ht := quadraticRFC_prefix_analytic fullMemory count A B (fun _ => g) 0 hA hB analyticAt_const
    Q hA0 hB0 hQ hpos hm (k+1) (fun j hj => hpre j (by omega))
  have hcont (j : Fin (k+1)) : ContinuousAt (fun t => V t j) 0 :=
    (ht.2 (k-j.val) (by omega)).2.1.continuousAt
  -- The actual normalized window bound controls each genuine raw observed residual, even when using zero-safe normalization.
  have hraw := raw_residual_order V G (fun t => ‖t‖^(count+1)) hcont hO ⟨k-i,by omega⟩
  have hindex : k-(k-i)=i := by omega
  have hraw' : (fun t => inner ℝ (probedStep m (A t) (B t) g i) (G t)) =O[𝓝 (0 : ℝ)] (fun t => ‖t‖^(count+1)) := by
    simpa only [V,hindex] using hraw
  exact hasDerivAt_zero_of_norm_order _ (count+1) (by omega) hraw'

/-- The real residual-variation vector of actual full-memory RFC is exactly zero for every genuine prefix of at least two steps and every positive finite correction count.
Use: The real residual-variation vector of actual full-memory RFC is exactly zero for every genuine prefix of at least two steps and every positive finite correction count.
Article: main_krylov, apB:eq:nu and thm:select, genuine full-memory RFC residual variation.
Proof: Apply the proved true zero derivative to each actually executed recorded-step residual and sum their genuine normalized zero coordinates. -/
theorem fullRFC_residualVariation_zero {n : ℕ} (count : ℕ) (hc : 0<count)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (A B : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ i, AnalyticAt ℝ (fun t => A t i) 0)
    (hB : ∀ i, AnalyticAt ℝ (fun t => B t i) 0)
    (hA0 : A 0=fun _ => cgOperator base) (hB0 : B 0=fun _ => cgOperator base)
    (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g) :
    residualVariation base g (rfcMethod fullMemory count) A B N=0 := by
  -- Every genuine residual coordinate is covered by the actual final noninitial RFC correction phase.
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N≠0)
  unfold residualVariation
  apply Finset.sum_eq_zero
  intro i _
  have hd := fullRFC_residual_zero_derivative count hc A B g hA hB (cgOperator base) hA0 hB0
    (cgOperator_positive base hb).1 (cgOperator_positive base hb).2 k (by omega)
    (fun j hj => cg_nonstagnation base hb g j (by omega)) i.val (by have := i.isLt;omega)
  rw [hd.deriv,zero_div,zero_smul]
end
end krylov.Envelope
