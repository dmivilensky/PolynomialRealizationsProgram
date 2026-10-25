import Mathlib.Tactic

/-! Exact endpoints of the admissible mass ratio for two finite columns.
The minimizer inequality is deliberately separate from these lag bounds. -/
noncomputable section
namespace polyak.Farey
open Finset

variable {ι : Type*}

def negativePositions (P : Finset ι) (A : ι→ℝ) : Finset ι := by
  classical
  exact P.filter (fun p=>A p < 0)

def lowerMassRatio (P : Finset ι) (A C : ι→ℝ)
    (hA : (negativePositions P A).Nonempty) : ℝ :=
  (negativePositions P A).sup' hA (fun p=> -A p/C p)

def upperMassRatio (P : Finset ι) (A C : ι→ℝ)
    (hC : (negativePositions P C).Nonempty) : ℝ :=
  (negativePositions P C).inf' hC (fun p=>A p/(-C p))

theorem two_columns_ratio_iff (P : Finset ι) (A C : ι→ℝ)
    (hA : (negativePositions P A).Nonempty) (hC : (negativePositions P C).Nonempty)
    (hsel : ∀p∈P,A p < 0→0 < C p) {r : ℝ} (hr : 0 < r) :
    (∀p∈P,0≤A p+r*C p) ↔ lowerMassRatio P A C hA≤r ∧r≤upperMassRatio P A C hC := by
  classical
  rw [lowerMassRatio,upperMassRatio,Finset.sup'_le_iff,Finset.le_inf'_iff]
  constructor
  · intro h
    constructor
    · intro p hp
      obtain ⟨hp,hAn⟩ := Finset.mem_filter.mp hp
      have hCp := hsel p hp hAn
      exact (div_le_iff₀ hCp).mpr (by linarith [h p hp])
    · intro p hp
      obtain ⟨hp,hCn⟩ := Finset.mem_filter.mp hp
      exact (le_div_iff₀ (neg_pos.mpr hCn)).mpr (by linarith [h p hp])
  · rintro ⟨hl,hu⟩ p hp
    by_cases hAn : A p < 0
    · have hb := (div_le_iff₀ (hsel p hp hAn)).mp (hl p (Finset.mem_filter.mpr ⟨hp,hAn⟩))
      linarith
    · by_cases hCn : C p < 0
      · have hb := (le_div_iff₀ (neg_pos.mpr hCn)).mp (hu p (Finset.mem_filter.mpr ⟨hp,hCn⟩))
        linarith
      · exact add_nonneg (le_of_not_gt hAn) (mul_nonneg hr.le (le_of_not_gt hCn))

theorem lowerMassRatio_pos (P : Finset ι) (A C : ι→ℝ)
    (hA : (negativePositions P A).Nonempty)
    (hsel : ∀p∈P,A p < 0→0 < C p) : 0 < lowerMassRatio P A C hA := by
  classical
  obtain ⟨p,hp⟩ := hA
  obtain ⟨hpP,hpA⟩ := Finset.mem_filter.mp hp
  exact (div_pos (neg_pos.mpr hpA) (hsel p hpP hpA)).trans_le (Finset.le_sup' (fun p=> -A p/C p) hp)

theorem two_columns_exists_iff (P : Finset ι) (A C : ι→ℝ)
    (hA : (negativePositions P A).Nonempty) (hC : (negativePositions P C).Nonempty) :
    (∃w0 wc : ℝ,0 < w0 ∧0 < wc ∧∀p∈P,0≤w0*A p+wc*C p) ↔
    (∀p∈P,A p < 0→0 < C p) ∧lowerMassRatio P A C hA≤upperMassRatio P A C hC := by
  constructor
  · rintro ⟨w0,wc,hw0,hwc,h⟩
    have hsel : ∀p∈P,A p < 0→0 < C p := by
      intro p hp hAn
      have hn : w0*A p < 0 := mul_neg_of_pos_of_neg hw0 hAn
      have hc : 0 < wc*C p := by linarith [h p hp]
      exact pos_of_mul_pos_right hc hwc.le
    refine ⟨hsel,?_⟩
    have he : ∀p∈P,0≤A p+(wc/w0)*C p := by
      intro p hp
      have hh := div_nonneg (h p hp) hw0.le
      have hid : (w0*A p+wc*C p)/w0=A p+(wc/w0)*C p := by field_simp [hw0.ne']
      rw [hid] at hh
      exact hh
    have hb := (two_columns_ratio_iff P A C hA hC hsel (div_pos hwc hw0)).mp he
    exact hb.1.trans hb.2
  · rintro ⟨hsel,hbound⟩
    have hr := lowerMassRatio_pos P A C hA hsel
    refine ⟨1,lowerMassRatio P A C hA,by norm_num,hr,?_⟩
    simpa only [one_mul] using
      (two_columns_ratio_iff P A C hA hC hsel hr).mpr ⟨le_rfl,hbound⟩

theorem two_columns_mass_ratio_iff (P : Finset ι) (A C : ι→ℝ)
    (hA : (negativePositions P A).Nonempty) (hC : (negativePositions P C).Nonempty)
    {w0 wc : ℝ} (hw0 : 0 < w0) (hwc : 0 < wc) :
    (∀p∈P,0≤w0*A p+wc*C p) ↔
    (∀p∈P,A p < 0 → 0 < C p) ∧
      lowerMassRatio P A C hA≤wc/w0 ∧ wc/w0≤upperMassRatio P A C hC := by
  have heq (p : ι) : (w0*A p+wc*C p)/w0=A p+(wc/w0)*C p := by
    field_simp [hw0.ne']
  constructor
  · intro h
    have hs := ((two_columns_exists_iff P A C hA hC).mp ⟨w0,wc,hw0,hwc,h⟩).1
    refine ⟨hs,(two_columns_ratio_iff P A C hA hC hs (div_pos hwc hw0)).mp ?_⟩
    intro p hp
    rw [←heq]
    exact div_nonneg (h p hp) hw0.le
  · rintro ⟨hs,hbound⟩ p hp
    have hh := (two_columns_ratio_iff P A C hA hC hs (div_pos hwc hw0)).mpr hbound p hp
    rw [←heq] at hh
    have hm := mul_nonneg hh hw0.le
    simpa only [div_mul_cancel₀ _ hw0.ne'] using hm

end polyak.Farey
