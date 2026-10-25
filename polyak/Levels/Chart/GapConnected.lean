import polyak.Levels.Chart.GapHomeomorphism
import Mathlib.Analysis.Convex.PathConnected

/-! The open root triangle times a positive amplitude ray is convex.
Subtracting the amplitude floor gives the actual connected gap. -/
noncomputable section
namespace polyak.Levels.Chart
open General Set

def rayParameterSet (K : ℕ) : Set ParameterSpace :=
  {p | 0<p.1 ∧ boundaryCosine K<p.2.1 ∧ p.2.1<p.2.2 ∧
    p.2.2<boundaryCosine (K+1)}
abbrev RayParameters (K : ℕ) := {p : ParameterSpace // p∈rayParameterSet K}

theorem convex_rayParameterSet (K : ℕ) : Convex ℝ (rayParameterSet K) := by
  have h₀ : IsLinearMap ℝ (fun p : ParameterSpace=>p.1) := ⟨by intros; rfl,by intros; rfl⟩
  have h₁ : IsLinearMap ℝ (fun p : ParameterSpace=>p.2.1) := ⟨by intros; rfl,by intros; rfl⟩
  have h₂ : IsLinearMap ℝ (fun p : ParameterSpace=>p.2.2) := ⟨by intros; rfl,by intros; rfl⟩
  have hd : IsLinearMap ℝ (fun p : ParameterSpace=>p.2.1-p.2.2) := by
    constructor
    · intros; dsimp; ring
    · intros; dsimp; ring
  have hh := (convex_halfSpace_gt h₀ 0).inter
    ((convex_halfSpace_gt h₁ (boundaryCosine K)).inter
      ((convex_halfSpace_lt hd 0).inter
        (convex_halfSpace_lt h₂ (boundaryCosine (K+1)))))
  convert hh using 1
  ext p
  simp only [rayParameterSet,mem_ofPred_eq,mem_inter_iff,sub_lt_zero]

theorem rayParameterSet_nonempty {K : ℕ} (hK : 2≤K) : (rayParameterSet K).Nonempty := by
  have hw := boundaryCosine_lt_succ hK
  refine ⟨(1,((2*boundaryCosine K+boundaryCosine (K+1))/3,
    (boundaryCosine K+2*boundaryCosine (K+1))/3)),?_,?_,?_,?_⟩ <;>
    dsimp <;> linarith

def rayToGap {K : ℕ} (p : RayParameters K) : GapParameters K :=
  ⟨(amplitudeFloor p.val.2.1 p.val.2.2+p.val.1,p.val.2.1,p.val.2.2),
    p.property.2.1,p.property.2.2.1,p.property.2.2.2,by linarith [p.property.1]⟩

theorem rayToGap_surjective (K : ℕ) : Function.Surjective (@rayToGap K) := by
  intro p
  refine ⟨⟨(p.val.1-amplitudeFloor p.val.2.1 p.val.2.2,p.val.2.1,p.val.2.2),
    sub_pos.mpr p.property.2.2.2,p.property.1,p.property.2.1,p.property.2.2.1⟩,?_⟩
  apply Subtype.ext
  dsimp [rayToGap]
  congr 1
  ring

theorem continuous_rayToGap {K : ℕ} (hK : 2≤K) : Continuous (@rayToGap K) := by
  apply Continuous.subtype_mk
  have hn₁ (p : RayParameters K) : 1-p.val.2.1≠0 := by
    have hu := p.property.2.2.1.trans (p.property.2.2.2.trans (boundaryCosine_succ_lt_one hK))
    exact ne_of_gt (sub_pos.mpr hu)
  have hn₂ (p : RayParameters K) : 1-p.val.2.2≠0 := by
    exact ne_of_gt (sub_pos.mpr (p.property.2.2.2.trans (boundaryCosine_succ_lt_one hK)))
  change Continuous (fun p : RayParameters K=>
    (2/((1-p.val.2.1)*(1-p.val.2.2))+p.val.1,p.val.2.1,p.val.2.2))
  fun_prop (disch := intro p; exact mul_ne_zero (hn₁ p) (hn₂ p))

theorem isConnected_gapParameterSet {K : ℕ} (hK : 2≤K) : IsConnected (gapParameterSet K) := by
  let : ConnectedSpace (RayParameters K) := isConnected_iff_connectedSpace.mp
    ((convex_rayParameterSet K).isConnected (rayParameterSet_nonempty hK))
  let : ConnectedSpace (GapParameters K) :=
    (rayToGap_surjective K).connectedSpace (continuous_rayToGap hK)
  exact isConnected_iff_connectedSpace.mpr inferInstance

theorem isConnected_gap {K : ℕ} (hK : 2≤K) : IsConnected {q : Tuning | Geometry.Gap K q} := by
  let : ConnectedSpace (GapParameters K) :=
    isConnected_iff_connectedSpace.mp (isConnected_gapParameterSet hK)
  let : ConnectedSpace (GapTunings K) :=
    (gapHomeomorph hK).symm.surjective.connectedSpace (gapHomeomorph hK).symm.continuous
  apply isConnected_iff_connectedSpace.mpr
  change ConnectedSpace (GapTunings K)
  infer_instance

end polyak.Levels.Chart
