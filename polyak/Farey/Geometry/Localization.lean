import polyak.Farey.Geometry.Grid
import polyak.Levels.Geometry.LevelZeroFull
import polyak.Levels.Geometry.DipTopology

/-! Farey localization is a statement about each actual periodic solution
measure: it has a positive-mass primitive atom in the closed dip. -/
noncomputable section
namespace polyak.Farey
open General Levels Levels.Geometry MeasureTheory Set

def Anchor (q : Tuning) (w : Measure Frequency) (ω : Frequency) : Prop :=
  0<w {ω} ∧ ω∈closedDip (tuningCurve q)

theorem gap_closedDip_window {q : Tuning} {K : ℕ} (hgap : Gap K q) :
    ∀ω∈closedDip (tuningCurve q),InWindow K ω := by
  have hc : closedDip (tuningCurve q)=closure (dip (tuningCurve q)) := by
    simpa only [shiftedCurve_zero] using closedDip_eq_closure_dip q 0
      (by simpa only [shiftedCurve_zero] using hgap.2.1)
  have hclosed : IsClosed {ω : Frequency | 2*Real.pi/((K:ℝ)+1)≤(ω:ℝ) ∧ (ω:ℝ)≤2*Real.pi/K} :=
    (isClosed_le continuous_const continuous_subtype_val).inter
      (isClosed_le continuous_subtype_val continuous_const)
  have hsub : closure (dip (tuningCurve q))⊆
      {ω : Frequency | 2*Real.pi/((K:ℝ)+1)≤(ω:ℝ) ∧ (ω:ℝ)≤2*Real.pi/K} :=
    hclosed.closure_subset_iff.mpr (fun ω hω=>⟨(hgap.2.2.1 ω hω).1.le,(hgap.2.2.1 ω hω).2.le⟩)
  intro ω hω
  have hw:=hsub (hc ▸ hω)
  have hθ : q.angle ω≤(ω:ℝ)/2 := hω
  constructor
  · apply lt_of_le_of_ne hw.1
    intro he
    rw [←he] at hθ
    have hh:=hgap.2.2.2.2
    have hn : (2*Real.pi/((K:ℝ)+1))/2=Real.pi/((K:ℝ)+1) := by ring
    rw [hn] at hθ
    linarith
  · apply lt_of_le_of_ne hw.2
    intro he
    rw [he] at hθ
    have hh:=hgap.2.2.2.1
    have hn : (2*Real.pi/(K:ℝ))/2=Real.pi/(K:ℝ) := by ring
    rw [hn] at hθ
    linarith

theorem finite_positive_mass_has_atom {w : Measure Frequency} {s : Set Frequency}
    (hs : s.Finite) (hw : 0<w s) : ∃ω∈s,0<w {ω} := by
  by_contra hn
  push Not at hn
  have hz : w (⋃ω∈s,({ω}:Set Frequency))=0 :=
    (measure_biUnion_null_iff hs.countable).mpr (fun ω hω=>
      le_antisymm (hn ω hω) bot_le)
  rw [Set.biUnion_of_singleton] at hz
  exact (ne_of_gt hw) hz

theorem periodic_solution_has_anchor {q : Tuning} {L : ℕ} (hL : 0<L)
    {w : Measure Frequency} (hw : ProgramSolution (tuningCurve q) nonzeroLags w)
    (hcarried : ∀ᵐω∂w,ω∈periodicGrid L) :
    ∃ω : Frequency,ω∈periodicGrid L ∧ Anchor q w ω := by
  have hp:=full_solution_closedDip_mass_pos hw
  have he : w (closedDip (tuningCurve q))=w (periodicGrid L∩closedDip (tuningCurve q)) := by
    apply measure_congr
    filter_upwards [hcarried] with ω hω
    simp only [Set.mem_inter_iff,hω,true_and]
  rw [he] at hp
  obtain ⟨ω,hω,hpos⟩:=finite_positive_mass_has_atom ((periodicGrid_finite hL).inter_of_left _) hp
  exact ⟨ω,hω.1,hpos,hω.2⟩

theorem window_minimal_denominator {K j k : ℕ} (hK : 2≤K) (hk : 0<k)
    (hj : 1≤j) (hwindow : 1/((K:ℝ)+1)<(j:ℝ)/k ∧ (j:ℝ)/k<1/(K:ℝ)) :
    2≤j ∧ 2*K+1≤k := by
  have hkR : (0:ℝ)<k := by positivity
  have hKR : (0:ℝ)<K := by positivity
  have hlo := (div_lt_div_iff₀ (by positivity : (0:ℝ)<K+1) hkR).mp hwindow.1
  have hhi := (div_lt_div_iff₀ hkR hKR).mp hwindow.2
  have hloR : (k:ℝ)<(j:ℝ)*(K+1) := by simpa only [one_mul] using hlo
  have hlo' : k<j*(K+1) := by exact_mod_cast hloR
  have hhiR : (j:ℝ)*K<k := by simpa only [one_mul] using hhi
  have hhi' : j*K<k := by exact_mod_cast hhiR
  have hj2 : 2≤j := by
    by_contra hn
    have hj1 : j=1 := by omega
    rw [hj1] at hlo' hhi'
    omega
  exact ⟨hj2,by nlinarith⟩

theorem farey_localization {q : Tuning} {K L : ℕ} (hgap : Gap K q) (hL : 0<L)
    {w : Measure Frequency} (hw : ProgramSolution (tuningCurve q) nonzeroLags w)
    (hcarried : ∀ᵐω∂w,ω∈periodicGrid L) :
    ∃(ω : Frequency)(j k : ℕ),Anchor q w ω ∧ 1≤j ∧ 2*j<k ∧ j.Coprime k ∧ k∣L ∧
      (ω:ℝ)=2*Real.pi*j/k ∧
      (1/((K:ℝ)+1)<(j:ℝ)/k ∧ (j:ℝ)/k<1/(K:ℝ)) ∧
      2*K+1≤k ∧ q.angle ω≤Real.pi*j/k ∧
      (¬ProgramSolution (tuningCurve q) nonzeroLags (Measure.dirac ω)→Real.pi/k<q.angle ω) := by
  obtain ⟨ω,hgrid,hanchor⟩:=periodic_solution_has_anchor hL hw hcarried
  obtain ⟨j,k,hj,hk,h2,hcop,hdiv,he⟩:=grid_primitive_coordinates hL hgrid
  have hwnd:=gap_closedDip_window hgap ω hanchor.2
  have hkr : (0:ℝ)<k := by positivity
  have hKR : (0:ℝ)<K := by positivity [hgap.1]
  have hwin : 1/((K:ℝ)+1)<(j:ℝ)/k ∧ (j:ℝ)/k<1/(K:ℝ) := by
    change 2*Real.pi/((K:ℝ)+1)<(ω:ℝ) ∧ (ω:ℝ)<2*Real.pi/K at hwnd
    rw [he] at hwnd
    constructor
    · have hh := (div_lt_div_iff₀ (by positivity : (0:ℝ)<K+1) hkr).mp hwnd.1
      apply (div_lt_div_iff₀ (by positivity : (0:ℝ)<K+1) hkr).mpr
      nlinarith [Real.pi_pos]
    · have hh := (div_lt_div_iff₀ hkr hKR).mp hwnd.2
      apply (div_lt_div_iff₀ hkr hKR).mpr
      nlinarith [Real.pi_pos]
  have hmin:=window_minimal_denominator hgap.1 hk hj hwin
  have hstrict : 2*j<k := by
    have hi:=closedDip_interior_frequency _ hanchor.2
    rw [he] at hi
    have hh:=(div_lt_iff₀ hkr).mp hi.2
    exact_mod_cast (show (2:ℝ)*j<k by nlinarith [Real.pi_pos])
  refine ⟨ω,j,k,hanchor,hj,hstrict,hcop,hdiv,he,hwin,hmin.2,?_,?_⟩
  · have hh : q.angle ω≤(ω:ℝ)/2:=hanchor.2
    rw [he] at hh
    rw [he]
    convert hh using 1
    ring
  · intro hnot
    apply lt_of_not_ge
    intro hθ
    exact hnot ((Lattice.rational_atom_program_iff (tuningCurve q) hcop (by omega) ω he).mpr hθ)

end polyak.Farey
