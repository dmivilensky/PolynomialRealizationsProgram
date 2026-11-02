import krylov.Convergence.VirtualTensorCubic
import krylov.Convergence.VirtualTensorBound
import krylov.Convergence.VirtualReferenceMidpoints
import krylov.OneGradient.TrialAmplitudes
import krylov.OneGradient.XRFCBidiagonal

/-!
Article: main_krylov, thm:V, uniform near-exact reference trials.
Use: bound all genuine amplitude multipliers, oblique flags and midpoint
weights on the original compact full-atom family. Source: the actual
primitive C2 trial charts, derived quadratic inverse domains, continuous
matrix inversion and the extreme-value theorem on compact sets (mathlib).
No bound on a response coefficient is a source assumption.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Metric krylov.Methods krylov.Reference krylov.Functions krylov.Stability
  krylov.OneGradient krylov.Secant krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The nonnegative true chronological amplitude after factoring out
its own reference trial error. Article: main_krylov, thm:V. -/
def xrfcTrialTailMagnitude (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ)
    (u : E) (l : ℕ) : ℝ :=
  let g := cgOperator base u
  let tau := fun j=>trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _=>cgOperator base) g j)
  (∏ j∈Finset.Ico (l+1) n,|(CG.length (cgOperator base) g j-tau j)/tau j|)*
    Real.sqrt (cgEnergy base g l)

/-- The actual amplitude factors without dividing by any trial error,
so exact reference searches are included. Article: thm:V. -/
theorem xrfcTrialCoefficient_abs_tail
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (u : E) (hc : referenceAtomCount base hb (cgOperator base u)=n)
    (l : ℕ) (hl : l<n) :
    |xrfcTrialCoefficient trial base (cgOperator base u) n l|=
      |xrfcTrialError trial base (cgOperator base u) l| * xrfcTrialTailMagnitude trial base u l := by
  rw [xrfc_trial_coefficient_abs trial base hb _ n l (by rw [hc];exact hl)]
  dsimp only [xrfcTrialError,xrfcTrialTailMagnitude]
  ring

/-- Every genuine reference factor in the near-exact tensor estimate
has a single finite compact bound, including both original stored bases.
Article: main_krylov, thm:V, uniformity over varying directions. -/
theorem xrfc_compact_trial_geometry
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (U : Set E) (hU : IsCompact U)
    (hcount : ∀ u∈U,referenceAtomCount base hb (cgOperator base u)=n)
    (ht : ∀ u∈U,∀ i<n,0<trial (oneGradientRun (xrfcMethod fullMemory trial)
      (fun _=>cgOperator base) (cgOperator base u) i))
    (hT : ∀ u∈U,∀ i<n,ContDiffAt ℝ 2 (trialCoordinate trial i)
      (oneGradientData (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i)) :
    ∃ B : ℝ,0<B ∧∀ u∈U,
      ∑ l∈Finset.range n,xrfcTrialTailMagnitude trial base u l*
        (1+‖cgOperator (transportedFlag (xrfcCanonicalColumns trial base (cgOperator base u)) l)‖)*
        ‖cgOperator (metricRoot base) (xrfcReferenceMidpointDrift trial (cgOperator base) u l)‖≤B := by
  let Q := cgOperator base
  let m := xrfcMethod fullMemory trial
  let S := fun u=>xrfcCanonicalColumns trial base (Q u)
  let W := fun u l=>xrfcReferenceMidpointDrift trial Q u l
  let F := fun u=>∑ l∈Finset.range n,xrfcTrialTailMagnitude trial base u l*
    (1+‖transportedFlag (S u) l‖)*‖cgOperator (metricRoot base) (W u l)‖
  have hF : ContinuousOn F U := by
    intro u hu
    have hp := cgOperator_positive base hb
    have hpre i (hi : i<n) := cg_nonstagnation base hb (Q u) i (by rw [hcount u hu];exact hi)
    have hA (i : ℕ) : ContDiffAt ℝ 2 (fun _ : E=>Q) u := contDiffAt_const
    have htraj := quadraticXRFC_prefix_contDiffAt trial (fun _ : E=>fun _=>Q) Q u
      hA Q.contDiff.contDiffAt Q rfl hp.1 hp.2 n hpre
      (fun i hi=>(ht u hu i hi).ne') (hT u hu)
    have htrial (j : ℕ) (hj : j<n) : ContinuousAt
        (fun v=>trial (oneGradientRun m (fun _=>Q) (Q v) j)) u :=
      (actual_trial_contDiffAt trial m (fun _ : E=>fun _=>Q) Q u j Q.contDiff.contDiffAt
        (fun i hi=>htraj.2 i (hi.trans hj))
        (fun i hi=>htraj.1 i (hi.trans hj.le)) (hT u hu j hj)).continuousAt
    have hcg (j : ℕ) (hj : j<n) := cg_prefix_contDiffAt (fun _ : E=>Q) Q u
      analyticAt_const (Q.analyticAt u) hp.1 hp.2 j (fun i hi=>hpre i (hi.trans hj)) 1
    have hlength (j : ℕ) (hj : j<n) : ContinuousAt (fun v=>CG.length Q (Q v) j) u := by
      have hd := (CG.invariant_line_pos Q hp.2 (Q u) j
        (CG.invariant Q hp.1 hp.2 (Q u) j (fun i hi=>hpre i (hi.trans hj))) (hpre j hj)).1
      exact ((hcg j hj).2.continuousAt.inner (hcg j hj).1.continuousAt).neg.div
        ((hcg j hj).2.continuousAt.inner (Q.continuous.continuousAt.comp (hcg j hj).2.continuousAt))
        (hp.2 _ hd).ne'
    have henergy (j : ℕ) (hj : j<n) : ContinuousAt (fun v=>Real.sqrt (cgEnergy base (Q v) j)) u := by
      have hs := (hlength j hj).smul (hcg j hj).2.continuousAt
      exact (hs.inner (Q.continuous.continuousAt.comp hs)).sqrt
    have htail (l : ℕ) (hl : l<n) : ContinuousAt (fun v=>xrfcTrialTailMagnitude trial base v l) u := by
      apply ContinuousAt.mul _ (henergy l hl)
      apply tendsto_finsetProd
      intro j hj
      have hjn := (Finset.mem_Ico.mp hj).2
      exact (((hlength j hjn).sub (htrial j hjn)).div (htrial j hjn) (ht u hu j hjn).ne').abs
    have hS : ContinuousAt S u := by
      apply continuousAt_pi.mpr
      intro a
      apply continuousAt_pi.mpr
      intro j
      change ContinuousAt (fun v=>∑ k : Fin n,metricRoot base a k*
        (oneGradientStep m (fun _=>Q) (Q v) j.val) k) u
      apply tendsto_finsetSum
      intro k _
      exact continuousAt_const.mul
        ((EuclideanSpace.proj k).continuous.continuousAt.comp (htraj.2 j.val j.isLt).continuousAt)
    have hSi : ContinuousAt (fun v=>(S v)⁻¹) u :=
      (continuousAt_matrix_inv (S u) (by
        simpa only [Ring.inverse_eq_inv'] using
          (continuousAt_inv₀ (isUnit_iff_ne_zero.mp (xrfc_columns_nonsingular trial base hb (Q u)
            (hcount u hu) (fun i hi=>(ht u hu i hi).ne')).2) :
              ContinuousAt (fun x : ℝ=>x⁻¹) (S u).det))).comp hS
    have hflag (l : ℕ) : ContinuousAt (fun v=>transportedFlag (S v) l) u :=
      (hS.mul continuousAt_const).mul hSi
    have hpoint (i : ℕ) (hi : i≤n) : ContinuousAt (fun v=>oneGradientReferencePoint m Q v i) u := by
      simp only [oneGradientReferencePoint,oneGradientRun_displacement_sum]
      apply continuousAt_id.add
      apply tendsto_finsetSum
      intro j hj
      exact (htraj.2 j ((Finset.mem_range.mp hj).trans_le hi)).continuousAt
    have hout : ContinuousAt (fun v=>oneGradientReferenceOutput m Q v n) u := by
      have hh := (quadraticXRFC_output_contDiffAt trial (fun _ : E=>fun _=>Q) (fun _=>Q) Q u
        hA contDiffAt_const Q.contDiff.contDiffAt Q rfl hp.1 hp.2 n hpre
        (fun i hi=>(ht u hu i hi).ne') (hT u hu)).1.continuousAt
      convert continuousAt_id.add hh using 1
      funext v
      dsimp only [oneGradientReferenceOutput,oneGradientReferencePoint,OneGradientMethod.outputDisplacement,
        Pi.add_apply,id_eq,m]
      abel
    have hmid (i : ℕ) : ContinuousAt (fun v=>oneGradientReferenceMidpoint m Q v n i) u := by
      dsimp only [oneGradientReferenceMidpoint]
      split_ifs with hi
      · exact ((hpoint i hi.le).add (hpoint (i+1) (by omega))).const_smul (1/2:ℝ)
      · exact ((hpoint n le_rfl).add hout).const_smul (1/2:ℝ)
    apply ContinuousAt.continuousWithinAt
    change ContinuousAt (fun v=>∑ l∈Finset.range n,xrfcTrialTailMagnitude trial base v l*
      (1+‖transportedFlag (S v) l‖)*‖cgOperator (metricRoot base) (W v l)‖) u
    apply tendsto_finsetSum
    intro l hl
    have hh : ContinuousAt (fun v=>xrfcTrialTailMagnitude trial base v l*
        (1+‖transportedFlag (S v) l‖)) u :=
      (htail l (Finset.mem_range.mp hl)).mul
        ((continuousAt_const : ContinuousAt (fun _ : E=>(1:ℝ)) u).add (hflag l).norm)
    have hw : ContinuousAt (fun v=>‖cgOperator (metricRoot base) (W v l)‖) u :=
      ((cgOperator (metricRoot base)).continuous.continuousAt.comp
      ((hmid (l+1)).sub (hmid l))).norm
    exact hh.mul hw
  obtain ⟨B,hB⟩ := hU.exists_bound_of_continuousOn hF
  refine ⟨max B 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro u hu
  have hh : F u≤max B 1 := (le_abs_self (F u)).trans ((hB u hu).trans (le_max_left _ _))
  dsimp only [F,S,W,Q] at hh
  simp_rw [Matrix.cstar_norm_def] at hh
  exact hh

end
end krylov.Convergence
