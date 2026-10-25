import polyak.ModeLocking.Localization.RegularSharp

/-! The article's distance between the complete competing grid and the
support is an actual finite minimum, with the exact lcm lower bound. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Levels MeasureTheory Set Metric
open scoped BigOperators
variable {q : General.Tuning} {t : ℝ} {L : ℕ}

def finiteGrid (M : ℕ) (hM : 3 ≤ M) : Finset Frequency :=
  (periodicGrid_finite (by omega : 0<M)).toFinset

theorem finiteGrid_nonempty (q : General.Tuning) (M : ℕ) (hM : 3 ≤ M) :
    (finiteGrid M hM).Nonempty := by
  obtain ⟨w,hw,hcar⟩ := Threshold.sigmaPeriodic_feasible q hM
  have : IsFiniteMeasure w := hw.1
  have : NeZero w := ⟨hw.2.1⟩
  obtain ⟨ω,hω⟩ := hcar.exists
  exact ⟨ω,by simpa only [finiteGrid,Set.Finite.mem_toFinset] using hω⟩

theorem gridIndex_nonempty (D : RegularData q t L) (M : ℕ) (hM : 3 ≤ M) :
    ((finiteGrid M hM).product (Finset.univ : Finset (Fin D.d))).Nonempty := by
  obtain ⟨ω,hω⟩ := finiteGrid_nonempty q M hM
  exact ⟨(ω,⟨0,D.d_pos⟩),Finset.mem_product.mpr ⟨hω,Finset.mem_univ _⟩⟩

def gridSupportDistance (D : RegularData q t L) (M : ℕ) (hM : 3 ≤ M) : ℝ :=
  ((finiteGrid M hM).product (Finset.univ : Finset (Fin D.d))).inf'
    (gridIndex_nonempty D M hM)
    (fun p => |(p.1:ℝ)-(D.atoms p.2:ℝ)|)

theorem gridSupportDistance_le (D : RegularData q t L) (M : ℕ) (hM : 3 ≤ M)
    {ω : Frequency} (hω : ω ∈ periodicGrid M) (i : Fin D.d) :
    gridSupportDistance D M hM ≤ |(ω:ℝ)-(D.atoms i:ℝ)| := by
  unfold gridSupportDistance
  apply Finset.inf'_le (b := (ω,i))
  exact Finset.mem_product.mpr ⟨by simpa only [finiteGrid,Set.Finite.mem_toFinset] using hω,
    Finset.mem_univ _⟩

theorem gridSupportDistance_pos (D : RegularData q t L) (M : ℕ) (hM : 3 ≤ M)
    (hdisj : ∀ i, D.atoms i ∉ periodicGrid M) : 0 < gridSupportDistance D M hM := by
  unfold gridSupportDistance
  rw [Finset.lt_inf'_iff]
  intro p hp
  apply abs_pos.mpr
  intro he
  have heq : p.1 = D.atoms p.2 := Subtype.ext (sub_eq_zero.mp he)
  have hg : p.1 ∈ periodicGrid M := by
    simpa only [finiteGrid,Set.Finite.mem_toFinset] using (Finset.mem_product.mp hp).1
  exact hdisj p.2 (heq ▸ hg)

theorem gridSupportDistance_lcm (D : RegularData q t L) (M : ℕ) (hM : 3 ≤ M)
    (hdisj : ∀ i, D.atoms i ∉ periodicGrid M) :
    2*Real.pi/(Nat.lcm L M:ℝ) ≤ gridSupportDistance D M hM := by
  unfold gridSupportDistance
  rw [Finset.le_inf'_iff]
  intro p hp
  have hg : p.1 ∈ periodicGrid M := by
    simpa only [finiteGrid,Set.Finite.mem_toFinset] using (Finset.mem_product.mp hp).1
  have hn : p.1 ≠ D.atoms p.2 := fun he => hdisj p.2 (he ▸ hg)
  simpa only [Nat.lcm_comm M L] using rational_grid_distance
    (by omega : 0<M) (by have hh := D.period_ge; omega : 0<L) hg (D.atoms_grid p.2) hn

theorem gridSupportDistance_le_infDist (D : RegularData q t L) (M : ℕ) (hM : 3 ≤ M)
    {ω : Frequency} (hω : ω ∈ periodicGrid M) :
    gridSupportDistance D M hM ≤ infDist (ω:ℝ) (regularSupport D:Set ℝ) := by
  rw [le_infDist (by simpa only [Finset.coe_nonempty] using regularSupport_nonempty D)]
  intro z hz
  obtain ⟨i,_hi,rfl⟩ := Finset.mem_image.mp hz
  simpa only [Real.dist_eq] using gridSupportDistance_le D M hM hω i

end polyak.ModeLocking.Localization
