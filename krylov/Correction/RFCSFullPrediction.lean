import krylov.Stability.RFCSProjectedOrders
import krylov.Correction.FullReconstruction
import krylov.Correction.ReferenceBasis
import krylov.Envelope.ResidualOrders

/-!
Article: main_krylov, thm:RFCS, genuine only-last-probe first-order expansion.
Use: the actual independently probed RFC-S executor has only its final
probe mismatch in the true first variation, with a derived quadratic remainder.
Source: actual analytic measured histories, the genuine predicted-model
projected residual, full reference rank and exact physical mismatch balance.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Methods krylov.Reference krylov.Stability krylov.Envelope krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator InnerProductSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {k : ℕ}

/-- The actual full augmented model-step family of the genuine independent-probe RFC-S run.
Use: reconstruct its full terminal residual through the original measured correction basis.
Article: main_krylov, thm:RFCS, genuine full terminal basis. -/
def rfcSFullStepBasis (Ap A B : ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (g : EuclideanSpace ℝ (Fin (k+1))) : Fin (k+1) → EuclideanSpace ℝ (Fin (k+1)) :=
  Fin.cons (rfcSDirection fullMemory Ap A B g k) (fun i : Fin k => rfcSStep fullMemory Ap A B g (k-1-i.val))

/-- The genuine RFC-S full reference basis equals the actual original quadratic RFC step/direction basis.
Use: derive true full reference rank from genuine CG nonstagnation.
Article: main_krylov, thm:RFCS, real full reference basis identification.
Proof: the exact-probe field identities give the actual current direction and every true previously evaluated stored step. -/
theorem rfcSFullStepBasis_reference (Q : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (g : EuclideanSpace ℝ (Fin (k+1))) :
    rfcSFullStepBasis (fun _ => Q) (fun _ => Q) (fun _ => Q) g=
      probedStepBasis (rfcMethod fullMemory 1) (fun _ => Q) (fun _ => Q) g k := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (rfcSFields_exact fullMemory (fun _ => Q) (fun _ => Q) g k).2.1
  · exact (rfcSFields_exact fullMemory (fun _ => Q) (fun _ => Q) g (k-1-j.val)).2.2.1

/-- The actual final RFC-S predicted-model correction has a genuinely quadratic full physical residual at every full active reference.
Use: all earlier independent-probe mismatches disappear from the actual first-order output.
Article: main_krylov, thm:RFCS, full corrected prediction is O(ω²).
Proof: real independent-probe prefix analyticity gives the actual full
moving basis. Genuine CG consistency gives its independently proved full
reference rank. The actual normalized predicted projected residual is
quadratic; zero-safe conversion returns its raw coordinates, and the proved
full inverse-transpose reconstruction yields the true physical vector order. -/
theorem full_rfcs_prediction_quadratic
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hN : k+1≤referenceAtomCount base hb g) (hk : 0<k)
    (Ap A B : X → ℕ → EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (hAp : ∀ i, AnalyticAt ℝ (fun x => Ap x i) 0)
    (hA : ∀ i, AnalyticAt ℝ (fun x => A x i) 0) (hB : ∀ i, AnalyticAt ℝ (fun x => B x i) 0)
    (hAp0 : Ap 0=(fun _ => cgOperator base)) (hA0 : A 0=(fun _ => cgOperator base))
    (hB0 : B 0=(fun _ => cgOperator base)) :
    (fun x => (rfcSPhase fullMemory (Ap x) (A x) (B x) g k).gradient) =O[𝓝 (0 : X)] (fun x => ‖x‖^2) := by
  -- Derive the actual moving basis and its true CG reference inverse before reconstructing the output.
  let Q := cgOperator base
  have hp := cgOperator_positive base hb
  have hm (j : ℕ) (_hj : CG.gradient Q g j≠0) (hjpos : 0<j) : 0<fullMemory j := hjpos
  have hpre (j : ℕ) (hj : j≤k) : CG.gradient Q g j≠0 := cg_nonstagnation base hb g j (hj.trans_lt (Nat.lt_succ_self k) |>.trans_le hN)
  have ht := quadraticRFCS_prefix_analytic fullMemory Ap A B (fun _ => g) 0 hAp hA hB analyticAt_const
    Q hAp0 hA0 hB0 hp.1 hp.2 hm (k+1) (fun j hj => hpre j (by omega))
  let U := fun x => rfcSFullStepBasis (Ap x) (A x) (B x) g
  let R := fun x => fullBasisMatrix (U x)
  let out := fun x => (rfcSPhase fullMemory (Ap x) (A x) (B x) g k).gradient
  have hU (i : Fin (k+1)) : AnalyticAt ℝ (fun x => U x i) 0 := by
    refine Fin.cases (ht.2 k (Nat.lt_succ_self k)).1 (fun j => ?_) i
    have hi := j.isLt
    exact (ht.2 _ (by omega)).2.1
  have hR (i j) : AnalyticAt ℝ (fun x => R x i j) 0 :=
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k+1) => ℝ) i).analyticAt _).comp (hU j)
  have hU0 : U 0=probedStepBasis (rfcMethod fullMemory 1) (fun _ => Q) (fun _ => Q) g k := by
    dsimp only [U]
    rw [hAp0,hA0,hB0]
    exact rfcSFullStepBasis_reference Q g
  have hu : IsUnit (R 0).det := fullBasisMatrix_unit _ (by
    rw [hU0]
    exact probedStepBasis_independent _ (rfcMethod_consistent fullMemory (fun _ hj => hj) 1) Q hp.1 hp.2 g k hpre)
  -- Lift the genuine quadratic projected residual through the real full basis.
  have hproj := (quadraticRFCS_predicted_projected_order fullMemory Ap A B (fun _ => g) hAp hA hB analyticAt_const
    Q hAp0 hA0 hB0 hp.1 hp.2 hm k hk hpre).2
  dsimp only at hproj
  rw [show min (fullMemory k) k=k from min_self k] at hproj
  have hproj' : (fun x => projectedResidual (unitWindow (U x)) (out x)) =O[𝓝 (0 : X)] (fun x => ‖x‖^2) := by
    simpa only [U,out,rfcSFullStepBasis,rfcSDirection] using hproj
  have hraw : (fun x => projectedResidual (U x) (out x)) =O[𝓝 (0 : X)] (fun x => ‖x‖^2) :=
    (euclidean_bigO_iff_entry _ _).mpr (raw_residual_order U out _ (fun i => (hU i).continuousAt) hproj')
  have hp' : (fun x => cgOperator (R x)ᵀ (out x)+(0 : EuclideanSpace ℝ (Fin (k+1)))) =O[𝓝 (0 : X)] (fun x => ‖x‖^(1+1)) := by
    simpa only [projectedResidual_fullBasisMatrix,add_zero,cgOperator] using hraw
  have hz : (fun _ : X => (0 : EuclideanSpace ℝ (Fin (k+1)))) =O[𝓝 (0 : X)] (fun x => ‖x‖^1) := isBigO_zero _ _
  have hf := full_projection_reconstruction_order_at R out (fun _ => 0) 1 hR hu hz hp'
  simpa only [map_zero,add_zero] using hf

end
end krylov.Correction

