import polyak.Global.Threshold.Parameters

/-! A continuous strictly decreasing real threshold family has a continuous
first crossing in (1,+infinity], with its actual order topology. Empty
crossing sets have infimum +infinity by the complete EReal order. -/
noncomputable section
namespace polyak.Global.Threshold
open Set Filter
open scoped Topology

variable {X : Type*} [TopologicalSpace X]

def crossingSet (F : X→ConditionNumber→ℝ) (p : X) : Set EReal :=
  {z | ∃κ : ConditionNumber,(κ.val:EReal)=z ∧ F p κ≤0}

def crossing (F : X→ConditionNumber→ℝ) (p : X) : EReal:=sInf (crossingSet F p)

omit [TopologicalSpace X] in
theorem crossing_le_of_nonpos (F : X→ConditionNumber→ℝ) (p : X) {κ : ConditionNumber}
    (h : F p κ≤0) : crossing F p≤(κ.val:EReal) := sInf_le ⟨κ,rfl,h⟩

omit [TopologicalSpace X] in
theorem le_crossing_of_positive {F : X→ConditionNumber→ℝ}
    (hanti : ∀p,StrictAnti (F p)) (p : X) {κ : ConditionNumber} (h : 0<F p κ) :
    (κ.val:EReal)≤crossing F p := by
  apply le_sInf
  rintro z ⟨η,rfl,hη⟩
  apply EReal.coe_le_coe_iff.mpr
  change κ≤η
  by_contra hn
  have hh:=(hanti p) (lt_of_not_ge hn)
  linarith

omit [TopologicalSpace X] in
theorem one_lt_crossing {F : X→ConditionNumber→ℝ}
    (hanti : ∀p,StrictAnti (F p)) (hpositive : ∀p,∃κ,0<F p κ) (p : X) :
    (1:EReal)<crossing F p := by
  obtain ⟨κ,hκ⟩:=hpositive p
  exact (EReal.coe_lt_coe_iff.mpr κ.property).trans_le (le_crossing_of_positive hanti p hκ)

lemma positive_to_right {f : ConditionNumber→ℝ} (hc : Continuous f) {κ : ConditionNumber}
    (h : 0<f κ) : ∃η : ConditionNumber,κ<η ∧ 0<f η := by
  have he : {η | 0<f η}∈𝓝 κ:=hc.continuousAt.eventually (eventually_gt_nhds h)
  obtain ⟨a,b,hab,hsub⟩:=mem_nhds_iff_exists_Ioo_subset.mp he
  obtain ⟨η,hκη,hηb⟩:=exists_between hab.2
  exact ⟨η,hκη,hsub ⟨hab.1.trans hκη,hηb⟩⟩

lemma negative_to_left {f : ConditionNumber→ℝ} (hc : Continuous f) {κ : ConditionNumber}
    (h : f κ<0) : ∃η : ConditionNumber,η<κ ∧ f η<0 := by
  have he : {η | f η<0}∈𝓝 κ:=hc.continuousAt.eventually (eventually_lt_nhds h)
  obtain ⟨a,b,hab,hsub⟩:=mem_nhds_iff_exists_Ioo_subset.mp he
  obtain ⟨η,haη,hηκ⟩:=exists_between hab.1
  exact ⟨η,hηκ,hsub ⟨haη,hηκ.trans hab.2⟩⟩

theorem crossing_le_iff_nonpos {F : X→ConditionNumber→ℝ}
    (hcont : Continuous (fun p : X×ConditionNumber=>F p.1 p.2))
    (hanti : ∀p,StrictAnti (F p)) (p : X) (κ : ConditionNumber) :
    crossing F p≤(κ.val:EReal) ↔ F p κ≤0 := by
  constructor
  · intro hc
    by_contra hn
    obtain ⟨η,hηκ,hη⟩:=positive_to_right (hcont.comp (continuous_const.prodMk continuous_id)) (lt_of_not_ge hn)
    have he : (η.val:EReal)≤(κ.val:EReal):=(le_crossing_of_positive hanti p hη).trans hc
    have hr:=EReal.coe_le_coe_iff.mp he
    exact (not_le_of_gt hηκ) hr
  · exact crossing_le_of_nonpos F p

theorem crossing_lt_iff_neg {F : X→ConditionNumber→ℝ}
    (hcont : Continuous (fun p : X×ConditionNumber=>F p.1 p.2))
    (hanti : ∀p,StrictAnti (F p)) (hpositive : ∀p,∃κ,0<F p κ)
    (p : X) (κ : ConditionNumber) : crossing F p<(κ.val:EReal) ↔ F p κ<0 := by
  constructor
  · intro h
    obtain ⟨r,hlo,hhi⟩:=EReal.exists_between_coe_real h
    have hr : 1<r:=EReal.coe_lt_coe_iff.mp ((one_lt_crossing hanti hpositive p).trans hlo)
    let η : ConditionNumber:=⟨r,hr⟩
    have he : F p η≤0 := (crossing_le_iff_nonpos hcont hanti p η).mp hlo.le
    have hηκ : η<κ:=EReal.coe_lt_coe_iff.mp hhi
    exact (hanti p hηκ).trans_le he
  · intro h
    obtain ⟨η,hηκ,hη⟩:=negative_to_left (hcont.comp (continuous_const.prodMk continuous_id)) h
    exact (crossing_le_of_nonpos F p hη.le).trans_lt (EReal.coe_lt_coe_iff.mpr hηκ)

theorem continuous_crossing {F : X→ConditionNumber→ℝ}
    (hcont : Continuous (fun p : X×ConditionNumber=>F p.1 p.2))
    (hanti : ∀p,StrictAnti (F p)) (hpositive : ∀p,∃κ,0<F p κ) : Continuous (crossing F) := by
  apply continuous_iff_lower_upperSemicontinuous.mpr
  constructor
  · intro p c hc
    have hm : max c 1<crossing F p:=max_lt hc (one_lt_crossing hanti hpositive p)
    obtain ⟨r,hrlo,hrhi⟩:=EReal.exists_between_coe_real hm
    have hr : 1<r:=EReal.coe_lt_coe_iff.mp ((le_max_right c 1).trans_lt hrlo)
    let κ : ConditionNumber:=⟨r,hr⟩
    have hf : 0<F p κ := by
      apply lt_of_not_ge
      intro hn
      have hh:=crossing_le_of_nonpos F p hn
      exact (not_le_of_gt hrhi) hh
    have hcF : Continuous (fun p : X=>F p κ):=hcont.comp (continuous_id.prodMk continuous_const)
    filter_upwards [hcF.continuousAt.eventually (eventually_gt_nhds hf)] with q hq
    exact ((le_max_left c 1).trans_lt hrlo).trans_le (le_crossing_of_positive hanti q hq)
  · intro p c hc
    obtain ⟨r,hrlo,hrhi⟩:=EReal.exists_between_coe_real hc
    have hr : 1<r:=EReal.coe_lt_coe_iff.mp ((one_lt_crossing hanti hpositive p).trans hrlo)
    let κ : ConditionNumber:=⟨r,hr⟩
    have hf : F p κ<0:=(crossing_lt_iff_neg hcont hanti hpositive p κ).mp hrlo
    have hcF : Continuous (fun p : X=>F p κ):=hcont.comp (continuous_id.prodMk continuous_const)
    filter_upwards [hcF.continuousAt.eventually (eventually_lt_nhds hf)] with q hq
    exact (crossing_le_of_nonpos F q hq.le).trans_lt hrhi

/-- The target subtype is exactly (1,+infinity], including its endpoint. -/
def crossingCondition (F : X→ConditionNumber→ℝ)
    (hanti : ∀p,StrictAnti (F p)) (hpositive : ∀p,∃κ,0<F p κ) (p : X) : ExtendedConditionNumber :=
  ⟨crossing F p,one_lt_crossing hanti hpositive p⟩

theorem continuous_crossingCondition {F : X→ConditionNumber→ℝ}
    (hcont : Continuous (fun p : X×ConditionNumber=>F p.1 p.2))
    (hanti : ∀p,StrictAnti (F p)) (hpositive : ∀p,∃κ,0<F p κ) :
    Continuous (crossingCondition F hanti hpositive) :=
  (continuous_crossing hcont hanti hpositive).subtype_mk _

omit [TopologicalSpace X] in
theorem crossing_eq_top_iff (F : X→ConditionNumber→ℝ) (p : X) :
    crossing F p=⊤ ↔ ∀κ : ConditionNumber,0<F p κ := by
  constructor
  · intro h κ
    apply lt_of_not_ge
    intro hn
    have hh:=crossing_le_of_nonpos F p hn
    rw [h] at hh
    exact (not_le_of_gt (EReal.coe_lt_top κ.val)) hh
  · intro h
    have he : crossingSet F p=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro z ⟨κ,rfl,hκ⟩
      exact (not_le_of_gt (h κ)) hκ
    simp only [crossing,he,sInf_empty]

end polyak.Global.Threshold
