import «2610.05164v2».Numerics.FlowStepData
import «2610.05164v2».Numerics.ValidatedFlow

/-!
Article: 2610.05164v2, Lemma 21.
`«2610.05164v2».Numerics.FlowStep.check_range_sound` propagates the accepted solution tube over the
whole step, not just its endpoint.
Interface: its result can discharge the corresponding enclosure premises of
`«2610.05164v2».Numerics.flowChainCheck_sound`.
Proof chain: 2610.05164v2, Theorem 3.6, via the general enclosure rules of Appendix F.2. This is a
reusable analytic interface, not a concrete full-dual acceptance claim.
Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.
-/
namespace «2610.05164v2».Numerics
open Set LeanCert.Core
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

/--
Membership in the specified domain/enclosure: `y (a+v)∈W.rangeEnclosure V`.

Use: `«2610.05164v2».Numerics.FlowStep.check_sound` uses this assertion to establish membership
in the specified domain/enclosure: `y (a+W.width)∈W.output`.

Article: 2610.05164v2, Lemma 21.

Source: 2610.05164v2, Appendix F.2 — finite rational enclosure rules and their real-function
semantics.

Proof: Separate `j=0` from its negation; prove the goal under each of these mutually exclusive
hypotheses.
-/
theorem FlowStep.check_range_sound (W : FlowStep) (hcheck : W.check=true)
    {C A B y : ℝ → ℝ} {a v : ℝ} {V : IntervalRat}
    (hcoeff : W.Coefficients C A B a)
    (hy : ContinuousOn y (Icc a (a+W.width)))
    (hyd : ∀ t∈Ioo a (a+W.width),HasDerivAt y (C t+A t*y t+B t*y t^2) t)
    (hy0 : y a∈W.initial) (hv : v∈Icc (0:ℝ) W.width) (hvV : v∈V) :
    y (a+v)∈W.rangeEnclosure V := by
  -- Separate `j=0` from its negation; prove the goal under each of these mutually exclusive
  -- hypotheses.
  rcases hcoeff with ⟨hC,hA,hB,hpoint,hwhole⟩
  have hp := hcheck
  simp only [FlowStep.check,Bool.and_eq_true,decide_eq_true_eq] at hp
  rcases hp with ⟨⟨⟨⟨hnums,htube⟩,hjp⟩,hjw⟩,_hout⟩
  have hh : 0<(W.width:ℝ) := by exact_mod_cast hnums.1
  have ha : a∈Icc a (a+W.width) := ⟨le_rfl,by linarith⟩
  have hs : UniqueDiffOn ℝ (Icc a (a+W.width)) := uniqueDiffOn_Icc (by linarith)
  have hbound (t : ℝ) (ht : t∈Icc a (a+W.width)) :
      C t∈jetAt W.wholeC 0 ∧ A t∈jetAt W.wholeA 0 ∧ B t∈jetAt W.wholeB 0 := by
    simpa only [normalizedWithin_zero] using hwhole t ht 0 (by omega)
  obtain ⟨z,hz0,hzY,hzd⟩ := flowTubeCheck_exists htube
    hC.continuousOn hA.continuousOn hB.continuousOn
    (fun t ht => (hbound t ht).1) (fun t ht => (hbound t ht).2.1)
    (fun t ht => (hbound t ht).2.2) (center_mem_hullPoint W.initial W.center)
  have hzs := riccati_solution_smooth (W.order+1) hC hA hB hzd
  obtain ⟨w,hw0,hwY,hwd⟩ := flowTubeCheck_exists htube
    hC.continuousOn hA.continuousOn hB.continuousOn
    (fun t ht => (hbound t ht).1) (fun t ht => (hbound t ht).2.1)
    (fun t ht => (hbound t ht).2.2) (mem_hullPoint hy0 W.center)
  have heq := riccati_unique hA.continuousOn hB.continuousOn hy
    (HasDerivWithinAt.continuousOn hwd) hyd
    (fun t ht => (hwd t ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)) hw0.symm
  have hyY : ∀ t∈Icc a (a+W.width),y t∈Icc (W.tube.lo:ℝ) W.tube.hi := by
    intro t ht
    rw [heq ht]
    exact hwY t ht
  have hzr := riccatiJetCheck_sound hjp hs ha
    ((hC a ha).of_le (by exact_mod_cast Nat.le_succ W.order))
    ((hA a ha).of_le (by exact_mod_cast Nat.le_succ W.order))
    ((hB a ha).of_le (by exact_mod_cast Nat.le_succ W.order))
    ((hzs a ha).of_le (by exact_mod_cast Nat.le_succ W.order)) hzd
    (fun j hj => (hpoint j hj).1) (fun j hj => (hpoint j hj).2.1)
    (fun j hj => (hpoint j hj).2.2) (by rw [hz0];exact IntervalRat.mem_singleton _)
  have hR : ∀ t∈Icc a (a+W.width),
      |normalizedWithin z (Icc a (a+W.width)) (W.order+1) t|≤W.remainder := by
    intro t ht
    have hr := riccatiJetCheck_sound hjw hs ht (hC t ht) (hA t ht) (hB t ht) (hzs t ht) hzd
      (fun j hj => (hwhole t ht j hj).1) (fun j hj => (hwhole t ht j hj).2.1)
      (fun j hj => (hwhole t ht j hj).2.2) (hzY t ht) (W.order+1) le_rfl
    rw [normalizedWithin_sub_const (by omega)] at hr
    apply abs_le.mpr
    constructor
    · have hlo : -(W.remainder:ℝ)≤(jetAt W.wholeR (W.order+1)).lo := by
        exact_mod_cast hnums.2.2.2.2.2.1
      exact hlo.trans hr.1
    · have hhi : ((jetAt W.wholeR (W.order+1)).hi:ℝ)≤W.remainder := by
        exact_mod_cast hnums.2.2.2.2.2.2
      exact hr.2.trans hhi
  have hr0 : |y a-(W.center:ℝ)|≤W.initialRadius := by
    have hlo : (W.center:ℝ)-W.initialRadius≤W.initial.lo := by exact_mod_cast hnums.2.2.2.1
    have hhi : (W.initial.hi:ℝ)≤W.center+W.initialRadius := by exact_mod_cast hnums.2.2.2.2.1
    apply abs_le.mpr
    constructor <;> linarith [hy0.1,hy0.2]
  have hL : ∀ t∈Ioo a (a+W.width),∀ v∈Icc (W.tube.lo:ℝ) W.tube.hi,
      A t+2*B t*v≤W.slope := by
    intro t ht v hv
    exact riccatiSlope_upper (hbound t ⟨ht.1.le,ht.2.le⟩).2.1
      (hbound t ⟨ht.1.le,ht.2.le⟩).2.2 hv
  have herr := riccati_taylor_propagation W.order hh hv hy hzs hyd
    (fun t ht => (hzd t ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    hyY hzY hz0 hr0 hR hL
  let P := ∑ j∈Finset.range (W.order+1),normalizedWithin z (Icc a (a+W.width)) j a*v^j
  have hP : P∈W.rangePolynomial V := by
    apply mem_sumIntervals
    intro j hj
    apply mem_roundHigh
    apply IntervalRat.mem_mul _ (mem_powerHigh hvV j)
    by_cases hj0 : j=0
    · simp only [hj0,normalizedWithin_zero,hz0]
      exact IntervalRat.mem_singleton _
    · simp only [ite_eq_right hj0]
      have hr := hzr j (by omega)
      simpa only [normalizedWithin_sub_const (Nat.pos_of_ne_zero hj0)] using hr
  have hE : (W.remainder:ℝ)*v^(W.order+1)+
      W.initialRadius*Real.exp ((W.slope:ℝ)*v)∈W.rangeError V := by
    apply IntervalRat.mem_add
      (IntervalRat.mem_mul (IntervalRat.mem_singleton _) (mem_powerHigh hvV _))
    apply IntervalRat.mem_mul (IntervalRat.mem_singleton _)
    exact mem_expHigh
      (IntervalRat.mem_mul (IntervalRat.mem_singleton W.slope) hvV)
  have hER : ((W.rangeError V).hi:ℝ)≤W.rangeRadius V := by exact_mod_cast le_max_right (0:ℚ) (W.rangeError V).hi
  have herrR : |y (a+v)-P|≤W.rangeRadius V := herr.trans (hE.2.trans hER)
  have hemem : y (a+v)-P∈(⟨-W.rangeRadius V,W.rangeRadius V,
      neg_le_self (le_max_left _ _)⟩:IntervalRat) := by
    simpa only [IntervalRat.mem_def,Rat.cast_neg] using abs_le.mp herrR
  simpa only [FlowStep.rangeEnclosure,add_sub_cancel] using IntervalRat.mem_add hP hemem

end
end «2610.05164v2».Numerics
