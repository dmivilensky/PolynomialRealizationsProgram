import polyak.GapEdges.Specialization.FanAnchors
import polyak.ModeLocking.Plateaus.IntrinsicSupport

/-! The anchor claim for the actual positive two-atomic fan measures:
their unique atom in the closed dip is on the side where the dip opens. -/
noncomputable section
namespace polyak.GapEdges
open General Levels ModeLocking Set Filter MeasureTheory
open scoped Topology BigOperators

theorem positive_pair_atom_iff (a c : Frequency) (wa wc : NNReal)
    (hwa : 0<wa) (hwc : 0<wc) (v : Frequency) :
    0<atomicMeasure ![wa,wc] ![a,c] {v} ↔ v=a ∨ v=c := by
  constructor
  · intro hp
    have hcar : ∀ᵐω∂atomicMeasure ![wa,wc] ![a,c],ω∈({a,c}:Set Frequency) := by
      unfold atomicMeasure
      rw [ae_finsetSum_measure_iff]
      intro i _
      apply Measure.ae_smul_measure
      fin_cases i <;> simp
    exact Plateaus.atom_mem_of_carried hcar hp
  · intro h
    rcases h with h|h
    · subst v
      exact Plateaus.atomicMeasure_atom_pos ![wa,wc] ![a,c] 0 hwa
    · subst v
      exact Plateaus.atomicMeasure_atom_pos ![wa,wc] ![a,c] 1 hwc

theorem actual_fan_anchors {q : Tuning} {k : ℕ}
    (A : FareyPlateau.Edge.AdjacentData q 1 k) (e : ℝ) (hχ : firstChi q k≠0) :
    ∀ᶠ δ : ℝ in 𝓝[≠] 0,∀a c : Frequency,
      (a:ℝ)=(A.frequency:ℝ)+δ →
      (c:ℝ)=(A.frequency:ℝ)-((k:ℝ)-1)*δ →
      ∀wa wc : NNReal,0<wa → 0<wc → ∀v : Frequency,
      (0<atomicMeasure ![wa,wc] ![a,c] {v} ∧
        v∈Geometry.closedDip (Geometry.shiftedCurve q (A.edgeShift-e*δ^2))) ↔
          (v=a ∧ firstChi q k*δ<0) ∨ (v=c ∧ 0<firstChi q k*δ) := by
  filter_upwards [fan_closedDip_side A e hχ] with δ hδ a c ha hc wa wc hwa hwc v
  obtain ⟨hnear,hfar⟩ := hδ a c ha hc
  rw [positive_pair_atom_iff a c wa wc hwa hwc v]
  constructor
  · rintro ⟨rfl|rfl,hv⟩
    · exact Or.inl ⟨rfl,hnear.mp hv⟩
    · exact Or.inr ⟨rfl,hfar.mp hv⟩
  · rintro (⟨rfl,hv⟩|⟨rfl,hv⟩)
    · exact ⟨Or.inl rfl,hnear.mpr hv⟩
    · exact ⟨Or.inr rfl,hfar.mpr hv⟩

theorem fan_anchor_opening_side {q : Tuning} {k : ℕ}
    (A : FareyPlateau.Edge.AdjacentData q 1 k) (e : ℝ) (hχ : firstChi q k≠0) :
    ∀ᶠ δ : ℝ in 𝓝[≠] 0,∀a c : Frequency,
      (a:ℝ)=(A.frequency:ℝ)+δ →
      (c:ℝ)=(A.frequency:ℝ)-((k:ℝ)-1)*δ →
      ∀wa wc : NNReal,0<wa → 0<wc → ∀v : Frequency,
      (0<atomicMeasure ![wa,wc] ![a,c] {v} ∧
        v∈Geometry.closedDip (Geometry.shiftedCurve q (A.edgeShift-e*δ^2))) →
          (firstChi q k<0 → 2*Real.pi/k<(v:ℝ)) ∧
          (0<firstChi q k → (v:ℝ)<2*Real.pi/k) := by
  filter_upwards [actual_fan_anchors A e hχ] with δ hδ a c ha hc wa wc hwa hwc v hv
  have hk : 0<(k:ℝ)-1 := by
    have hh : (3:ℝ)≤k := by exact_mod_cast A.period_ge
    linarith
  have hanchor := (hδ a c ha hc wa wc hwa hwc v).mp hv
  rw [Junction.adjacent_frequency_one A] at ha hc
  rcases hanchor with ⟨rfl,hp⟩|⟨rfl,hp⟩
  · constructor <;> intro hsign <;> nlinarith
  · constructor <;> intro hsign
    · have hδneg : δ<0 := by nlinarith
      nlinarith
    · have hδpos : 0<δ := by nlinarith
      nlinarith

theorem fan_unique_anchor {q : Tuning} {k : ℕ}
    (A : FareyPlateau.Edge.AdjacentData q 1 k) (e : ℝ) (hχ : firstChi q k≠0) :
    ∀ᶠ δ : ℝ in 𝓝[≠] 0,∀a c : Frequency,
      (a:ℝ)=(A.frequency:ℝ)+δ →
      (c:ℝ)=(A.frequency:ℝ)-((k:ℝ)-1)*δ →
      ∀wa wc : NNReal,0<wa → 0<wc →
      ∃!v : Frequency,0<atomicMeasure ![wa,wc] ![a,c] {v} ∧
        v∈Geometry.closedDip (Geometry.shiftedCurve q (A.edgeShift-e*δ^2)) := by
  filter_upwards [actual_fan_anchors A e hχ,self_mem_nhdsWithin] with δ hδ hδ0 a c ha hc wa wc hwa hwc
  have hnonzero : δ≠0 := hδ0
  have he := hδ a c ha hc wa wc hwa hwc
  rcases lt_or_gt_of_ne (mul_ne_zero hχ hnonzero) with hneg|hpos
  · refine ⟨a,(he a).mpr (Or.inl ⟨rfl,hneg⟩),?_⟩
    intro v hv
    rcases (he v).mp hv with ⟨hv,_⟩|⟨_,hp⟩
    · exact hv
    · linarith
  · refine ⟨c,(he c).mpr (Or.inr ⟨rfl,hpos⟩),?_⟩
    intro v hv
    rcases (he v).mp hv with ⟨_,hn⟩|⟨hv,_⟩
    · linarith
    · exact hv

end polyak.GapEdges
