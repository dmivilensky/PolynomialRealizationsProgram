import polyak.ModeLocking.Localization.AnalyticSymbol
import polyak.ModeLocking.Localization.Quadratic
import polyak.ModeLocking.Analysis.MarkedCoercivity

/-! Finite nondegenerate interior zeros give quadratic localization for all
shifts, including a positive minimizer coefficient and arbitrary measures. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Levels MeasureTheory Set Metric
open scoped BigOperators
variable {I : Type*} [Fintype I]

theorem quadratic_localization (q : General.Tuning) (t : ℝ) (n : I → ℤ)
    (a : I → ℝ) (γ : ℝ) (ha : ∀ i, 0 ≤ a i) (hγ : 0 ≤ γ)
    (hnorm : (∑ i, a i)+γ=1)
    (hT : ∀ ω, symbol q t n a γ ω ≤ 0)
    (Z : Finset ℝ) (hZ : ∀ z ∈ Z, z ∈ Ioo 0 Real.pi)
    (hzeros : ∀ x ∈ Ioo 0 Real.pi, extendedSymbol q t n a γ x=0 ↔ x ∈ Z)
    (hcurv : ∀ z ∈ Z, iteratedDeriv 2 (extendedSymbol q t n a γ) z < 0)
    (hpi : extendedSymbol q t n a γ Real.pi < 0)
    (hzero : γ=0 → iteratedDeriv 2 (extendedSymbol q t n a γ) 0 < 0) :
    ∃ c > 0, ∀ s, t ≤ s → ∀ w : Measure Frequency, IsFiniteMeasure w →
      (0 ≤ ∫ ω, symbol q s n a γ ω ∂w) →
      (∫ ω, (infDist (ω:ℝ) ((insert 0 Z : Finset ℝ):Set ℝ))^2 ∂w) ≤
        (2*(s-t)/c)*w.real univ := by
  classical
  let f := extendedSymbol q t n a γ
  let A := insert 0 Z
  have hnonpos (x : ℝ) (hx : x ∈ Icc 0 Real.pi) : f x ≤ 0 := by
    have hh := hT ⟨x,hx⟩
    rwa [← extendedSymbol_actual] at hh
  have hAz (z : ℝ) (hz : z ∈ A) : z ∈ Icc 0 Real.pi := by
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact ⟨le_rfl,Real.pi_pos.le⟩
    · exact ⟨(hZ z hz).1.le,(hZ z hz).2.le⟩
  have hslope (z : ℝ) (hz : z ∈ A) (hfz : f z=0) : deriv f z=0 := by
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact extendedSymbol_deriv_zero q t n a γ
    · apply IsLocalMax.deriv_eq_zero
      filter_upwards [Ioo_mem_nhds (hZ z hz).1 (hZ z hz).2] with x hx
      rw [hfz]
      exact hnonpos x ⟨hx.1.le,hx.2.le⟩
  have hcurvature (z : ℝ) (hz : z ∈ A) (hfz : f z=0) : iteratedDeriv 2 f z<0 := by
    rcases Finset.mem_insert.mp hz with rfl | hz
    · apply hzero
      have he : f 0 = -γ := by
        change extendedSymbol q t n a γ (frequencyZero:ℝ) = -γ
        rw [extendedSymbol_actual,symbol_zero]
      linarith
    · exact hcurv z hz
  have hstrict (x : ℝ) (hx : x ∈ Icc 0 Real.pi) (hnot : x ∉ A) : f x<0 := by
    have hx0 : x ≠ 0 := fun he => hnot (Finset.mem_insert.mpr (Or.inl he))
    by_cases hxp : x=Real.pi
    · simpa only [hxp] using hpi
    have hxi : x ∈ Ioo 0 Real.pi :=
      ⟨lt_of_le_of_ne hx.1 hx0.symm,lt_of_le_of_ne hx.2 hxp⟩
    apply lt_of_le_of_ne (hnonpos x hx)
    intro he
    exact hnot (Finset.mem_insert.mpr (Or.inr ((hzeros x hxi).mp he)))
  obtain ⟨c₀,hc₀,hcineq⟩ := Analysis.finite_marked_zero_coercivity
    (Finset.insert_nonempty 0 Z) hAz
    (fun x hx => (analyticAt_extendedSymbol q t n a γ x hx).contDiffAt)
    (continuousOn_extendedSymbol_second q t n a γ) hnonpos hslope hcurvature hstrict
  apply quadratic_localization_of_coercivity q t n a γ ha hγ hnorm
    (fun ω => infDist (ω:ℝ) (A:Set ℝ))
  · exact (continuous_infDist_pt (A:Set ℝ)).comp continuous_subtype_val
  · intro ω
    refine ⟨infDist_nonneg,?_⟩
    have hh : infDist (ω:ℝ) (A:Set ℝ) ≤ dist (ω:ℝ) 0 :=
      infDist_le_dist_of_mem (show (0:ℝ) ∈ (A:Set ℝ) from Finset.mem_insert_self _ _)
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg ω.property.1] using hh.trans
      (by simpa only [Real.dist_eq,sub_zero,abs_of_nonneg ω.property.1] using ω.property.2)
  · exact hc₀
  · intro ω
    have hh := hcineq (ω:ℝ) ω.property
    rwa [extendedSymbol_actual] at hh

end polyak.ModeLocking.Localization
