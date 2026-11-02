import krylov.Envelope.MovingSpanJet
import krylov.Methods.CorrectionTraceGeometry
import Mathlib.Data.List.GetD

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:filtration, genuine complete correction-program first jets.
Use: control the actual total correction and every true intermediate query
and returned-gradient first derivative on a zero reference phase. Genuine
primitive coefficient regularity and real moving-span constraints supply all
actual derivative hypotheses; no residual or cycle expansion is assumed.
Source: the proved actual finite program trace regularity and fixed query
count, true trace span geometry and genuine zero-query moving-span derivative.
-/

namespace krylov.Envelope
noncomputable section
open Filter Topology Matrix krylov.Methods krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m p : ℕ}

/-- A genuine regular finite zero-reference correction program has its true movement and every actual queried-vector derivative in the reference span, while every actual intermediate-gradient shift derivative lies in its true reference operator image span.
Use: A genuine regular finite zero-reference correction program has its true movement and every actual queried-vector derivative in the reference span, while every actual intermediate-gradient shift derivative lies in its true reference operator image span.
Article: main_krylov, apB:lem:filtration, genuine complete correction-program first jets.
Proof: Derive actual total-movement and complete observed-trace C-two regularity from primitive programs. Real zero corrections and exact trace span geometry give zero reference values and actual moving-span constraints. Apply the genuine moving-span derivative theorem to the real movement and each actual fixed query coordinate; the actual finite trace length justifies every observed read. -/
theorem correction_program_zero_jets (P : CorrectionProgram E m)
    (B : ℝ → E →L[ℝ] E) (g : ℝ → E) (data : ℝ → Fin m → E) (s : ℝ → Fin p → E)
    (hB : ContDiffAt ℝ 2 B 0) (hg : ContDiffAt ℝ 2 g 0) (hd : ContDiffAt ℝ 2 data 0)
    (hs : ∀ i, ContDiffAt ℝ 2 (fun t => s t i) 0)
    (hP : P.RegularAt 2 (B 0) (g 0) (data 0))
    (hzero : ZeroCorrections (P.tree (data 0)) (B 0) (g 0))
    (hspan : ∀ᶠ t in 𝓝 (0 : ℝ), (P.tree (data t)).InSubspace (Submodule.span ℝ (Set.range (s t))))
    (hGram : (crossGram (s 0) (s 0)).det≠0)
    (hImageGram : (crossGram (fun i => B 0 (s 0 i)) (fun i => B 0 (s 0 i))).det≠0) :
    let R := fun t => runCorrections (P.tree (data t)) (B t) (g t)
    deriv (fun t => (R t).movement) 0∈Submodule.span ℝ (Set.range (s 0)) ∧
      ∀ j : Fin P.queryCount,
        deriv (fun t => ((R t).trace.getD j.val (0,0)).1) 0∈Submodule.span ℝ (Set.range (s 0)) ∧
        deriv (fun t => ((R t).trace.getD j.val (0,0)).2-g t) 0∈
          Submodule.span ℝ (Set.range fun i => B 0 (s 0 i)) := by
  -- Use the actual finite correction executor and its proved true complete-trace regularity.
  let R := fun t => runCorrections (P.tree (data t)) (B t) (g t)
  have hR := P.run_regular B g data 0 hB hg hd hP
  have hM0 : (R 0).movement=0 := (zeroCorrections_change_operator _ (B 0) (B 0) (g 0) hzero).2.1
  have hMs : ∀ᶠ t in 𝓝 (0 : ℝ), (R t).movement∈Submodule.span ℝ (Set.range (s t)) :=
    hspan.mono fun t ht => runCorrections_movement_mem _ _ _ _ ht
  refine ⟨zero_moving_span_derivative s _ (fun i => (hs i).of_le (by norm_num))
    (hR.1.of_le (by norm_num)) hM0 hGram hMs,?_⟩
  intro j
  -- The primitive program has a proved genuine query count for every real input, so these coordinates are actual observations.
  have hj (t : ℝ) : j.val < (R t).trace.length := by
    change j.val < (runCorrections _ _ _).trace.length
    rw [P.trace_length]
    exact j.isLt
  have hmem (t : ℝ) : (R t).trace.getD j.val (0,0)∈(R t).trace := by
    rw [List.getD_eq_get _ _ ⟨j.val,hj t⟩]
    exact List.get_mem _ _
  have hz := zeroCorrections_trace _ _ _ hzero _ (hmem 0)
  have hu : ContDiffAt ℝ 2 (fun t => ((R t).trace.getD j.val (0,0)).1) 0 := by
    convert hR.2.2.getD (2*j.val) using 1
    funext t
    exact (correctionObservations_getD_even (R t).trace (0 : E) j.val).symm
  have hq : ∀ᶠ t in 𝓝 (0 : ℝ), ((R t).trace.getD j.val (0,0)).1∈Submodule.span ℝ (Set.range (s t)) :=
    hspan.mono fun t ht => (correction_trace_mem _ _ _ _ ht _ (hmem t)).1
  refine ⟨zero_moving_span_derivative s _ (fun i => (hs i).of_le (by norm_num))
    (hu.of_le (by norm_num)) hz.1 hGram hq,?_⟩
  have hv : ContDiffAt ℝ 2 (fun t => ((R t).trace.getD j.val (0,0)).2) 0 := by
    convert hR.2.2.getD (2*j.val+1) using 1
    funext t
    exact (correctionObservations_getD_odd (R t).trace (0 : E) j.val).symm
  have hv0 : ((R 0).trace.getD j.val (0,0)).2-g 0=0 := by rw [hz.2,sub_self]
  -- Every true intermediate gradient shift lies in the genuine image of the same actual moving correction span.
  have hvs : ∀ᶠ t in 𝓝 (0 : ℝ), ((R t).trace.getD j.val (0,0)).2-g t∈
      Submodule.span ℝ (Set.range fun i => B t (s t i)) := by
    filter_upwards [hspan] with t ht
    have hp := (correction_trace_mem _ _ _ _ ht _ (hmem t)).2
    have hmap : (Submodule.span ℝ (Set.range (s t))).map (B t).toLinearMap ≤
        Submodule.span ℝ (Set.range fun i => B t (s t i)) := by
      apply Submodule.map_le_iff_le_comap.mpr
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact Submodule.subset_span ⟨i,rfl⟩
    exact hmap hp
  exact zero_moving_span_derivative (fun t i => B t (s t i)) _
    (fun i => (hB.clm_apply (hs i)).of_le (by norm_num)) ((hv.sub hg).of_le (by norm_num)) hv0 hImageGram hvs
end
end krylov.Envelope
