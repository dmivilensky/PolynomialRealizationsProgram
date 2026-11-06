import nesterov.Quadratic.Basic

/-!
Article: §2, Lemma quadratic stability and the actual maximum defining ρq.
Use: the maximum ranges over every curvature and every actual complex root.
-/

noncomputable section
namespace nesterov.Quadratic

def rootNorms (μ L β τ h : ℝ) : Set ℝ :=
  {r | ∃ lam ∈ Set.Icc μ L, ∃ z : ℂ, characteristic β τ h lam z = 0 ∧ r = ‖z‖}

def quadraticRate (μ L β τ h : ℝ) : ℝ := sSup (rootNorms μ L β τ h)

def Stable (μ L β τ h : ℝ) : Prop :=
  ∀ lam ∈ Set.Icc μ L, ∀ z : ℂ, characteristic β τ h lam z = 0 → ‖z‖ < 1

theorem stable_iff {μ L β τ h : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hh : 0 < h) (_hβ : 0 ≤ β) (hβ1 : β < 1) (hτ : 0 ≤ τ) :
    Stable μ L β τ h ↔ h * L * (1 + 2 * τ) < 2 * (1 + β) := by
  constructor
  · intro hstable
    have hlast : ∀ z : ℂ, z ^ 2 - (S β τ h L : ℂ) * z + (Q β τ h L : ℂ) = 0 → ‖z‖ < 1 := by
      intro z hz
      apply hstable L ⟨hL.le, le_rfl⟩ z
      rwa [characteristic_eq]
    have ha := (abs_lt.mp (roots_stable_iff.mp hlast).2).1
    dsimp [S, Q] at ha
    nlinarith
  · intro hmargin lam hlam z hz
    have hlampos : 0 < lam := hμ.trans_le hlam.1
    have hhl : h * lam ≤ h * L := mul_le_mul_of_nonneg_left hlam.2 hh.le
    have hm : h * lam * (1 + 2 * τ) < 2 * (1 + β) :=
      (mul_le_mul_of_nonneg_right hhl (by linarith)).trans_lt hmargin
    have hq : Q β τ h lam < 1 := by
      dsimp [Q]
      nlinarith [mul_nonneg (mul_pos hh hlampos).le hτ]
    have ha : |S β τ h lam| < 1 + Q β τ h lam := by
      rw [abs_lt]
      dsimp [S, Q]
      constructor <;> nlinarith [mul_pos hh hlampos]
    exact root_norm_lt_one hq ha (by rwa [← characteristic_eq])

theorem rootNorms_nonempty {μ L : ℝ} (hμL : μ ≤ L) (β τ h : ℝ) :
    (rootNorms μ L β τ h).Nonempty := by
  obtain ⟨z, hz⟩ := polyak.Dynamics.exists_complex_quadratic_root (S β τ h μ) (Q β τ h μ)
  exact ⟨‖z‖, μ, ⟨le_rfl, hμL⟩, z, by rwa [characteristic_eq], rfl⟩

def coefficientBound (μ L β τ h : ℝ) : ℝ :=
  1 + |1 + β| + |β| + |h| * max |μ| |L| * (|1 + τ| + |τ|)

theorem root_norm_le_coefficientBound {μ L β τ h lam : ℝ}
    (hlam : lam ∈ Set.Icc μ L) {z : ℂ} (hz : characteristic β τ h lam z = 0) :
    ‖z‖ ≤ coefficientBound μ L β τ h := by
  have hlamabs : |lam| ≤ max |μ| |L| := by
    rw [abs_le]
    constructor
    · linarith [neg_abs_le μ, le_max_left |μ| |L|, hlam.1]
    · linarith [le_abs_self L, le_max_right |μ| |L|, hlam.2]
  have hS : |S β τ h lam| ≤ |1 + β| + |h| * max |μ| |L| * |1 + τ| := by
    calc
      _ ≤ |1 + β| + |h * lam * (1 + τ)| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_mul, abs_mul]
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlamabs (abs_nonneg h)) (abs_nonneg (1 + τ)))
  have hQ : |Q β τ h lam| ≤ |β| + |h| * max |μ| |L| * |τ| := by
    calc
      _ ≤ |β| + |h * lam * τ| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_mul, abs_mul]
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlamabs (abs_nonneg h)) (abs_nonneg τ))
  have hb := root_norm_bound (by rwa [← characteristic_eq] :
    z ^ 2 - (S β τ h lam : ℂ) * z + (Q β τ h lam : ℂ) = 0)
  dsimp [coefficientBound]
  nlinarith only [hS, hQ, hb]

/-- Compactness and hence attainment do not require quadratic stability. -/
theorem isCompact_rootNorms (μ L β τ h : ℝ) : IsCompact (rootNorms μ L β τ h) := by
  let R : Set (ℝ × ℂ) := {p | p.1 ∈ Set.Icc μ L ∧ characteristic β τ h p.1 p.2 = 0}
  have hclosed : IsClosed R := by
    apply (isClosed_Icc.preimage continuous_fst).inter
    apply isClosed_eq _ continuous_const
    unfold characteristic queryPolynomial
    fun_prop
  have hcompact : IsCompact R := by
    apply (isCompact_Icc.prod
      (isCompact_closedBall (0 : ℂ) (coefficientBound μ L β τ h))).of_isClosed_subset hclosed
    intro p hp
    exact ⟨hp.1, by simpa using root_norm_le_coefficientBound hp.1 hp.2⟩
  have himage : (fun p : ℝ × ℂ => ‖p.2‖) '' R = rootNorms μ L β τ h := by
    ext r
    constructor
    · rintro ⟨⟨lam, z⟩, hp, rfl⟩
      exact ⟨lam, hp.1, z, hp.2, rfl⟩
    · rintro ⟨lam, hlam, z, hz, rfl⟩
      exact ⟨(lam, z), ⟨hlam, hz⟩, rfl⟩
  rw [← himage]
  exact hcompact.image (continuous_norm.comp continuous_snd)

theorem quadraticRate_isGreatest_general {μ L β τ h : ℝ} (hμL : μ ≤ L) :
    IsGreatest (rootNorms μ L β τ h) (quadraticRate μ L β τ h) := by
  obtain ⟨r, hr⟩ := (isCompact_rootNorms μ L β τ h).exists_isGreatest
    (rootNorms_nonempty hμL β τ h)
  simpa only [quadraticRate, hr.csSup_eq] using hr

theorem quadraticRate_nonneg_general {μ L β τ h : ℝ} (hμL : μ ≤ L) :
    0 ≤ quadraticRate μ L β τ h := by
  obtain ⟨lam, _, z, _, he⟩ := (quadraticRate_isGreatest_general hμL).1
  rw [he]
  exact norm_nonneg z

theorem root_norm_le_rate_general {μ L β τ h lam : ℝ} (hμL : μ ≤ L)
    (hlam : lam ∈ Set.Icc μ L) {z : ℂ} (hz : characteristic β τ h lam z = 0) :
    ‖z‖ ≤ quadraticRate μ L β τ h :=
  (quadraticRate_isGreatest_general hμL).2 ⟨lam, hlam, z, hz, rfl⟩

theorem quadraticRate_pos {μ L β τ h : ℝ} (hL : μ < L) (hh : 0 < h) (hτ : 0 ≤ τ) :
    0 < quadraticRate μ L β τ h := by
  by_contra hn
  have hzero : quadraticRate μ L β τ h = 0 :=
    le_antisymm (not_lt.mp hn) (quadraticRate_nonneg_general hL.le)
  have hS (lam : ℝ) (hlam : lam ∈ Set.Icc μ L) : S β τ h lam = 0 := by
    obtain ⟨z, w, hz, hw, hs, _⟩ := root_pair (S β τ h lam) (Q β τ h lam)
    have hz' : characteristic β τ h lam z = 0 := by rwa [characteristic_eq]
    have hw' : characteristic β τ h lam w = 0 := by rwa [characteristic_eq]
    have hznorm := root_norm_le_rate_general hL.le hlam hz'
    have hwnorm := root_norm_le_rate_general hL.le hlam hw'
    rw [hzero] at hznorm hwnorm
    have hz0 : z = 0 := norm_eq_zero.mp (le_antisymm hznorm (norm_nonneg z))
    have hw0 : w = 0 := norm_eq_zero.mp (le_antisymm hwnorm (norm_nonneg w))
    rw [hz0, hw0, zero_add] at hs
    exact_mod_cast hs.symm
  have hfirst := hS μ (Set.left_mem_Icc.mpr hL.le)
  have hlast := hS L (Set.right_mem_Icc.mpr hL.le)
  dsimp [S] at hfirst hlast
  have hp := mul_pos (mul_pos hh (sub_pos.mpr hL)) (show 0 < 1 + τ by linarith)
  nlinarith

theorem stable_iff_quadraticRate_lt_one {μ L β τ h : ℝ} (hμL : μ ≤ L) :
    Stable μ L β τ h ↔ quadraticRate μ L β τ h < 1 := by
  constructor
  · intro hstable
    obtain ⟨lam, hlam, z, hz, he⟩ := (quadraticRate_isGreatest_general hμL).1
    rw [he]
    exact hstable lam hlam z hz
  · intro hrate lam hlam z hz
    exact ((quadraticRate_isGreatest_general hμL).2 ⟨lam, hlam, z, hz, rfl⟩).trans_lt hrate

theorem quadraticRate_lt_one_iff {μ L β τ h : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (hh : 0 < h) (hβ : 0 ≤ β) (hβ1 : β < 1) (hτ : 0 ≤ τ) :
    quadraticRate μ L β τ h < 1 ↔ h * L * (1 + 2 * τ) < 2 * (1 + β) := by
  rw [← stable_iff_quadraticRate_lt_one hL.le]
  exact stable_iff hμ hL hh hβ hβ1 hτ

theorem isCompact_rootNorms_of_stable {μ L β τ h : ℝ}
    (hstable : Stable μ L β τ h) : IsCompact (rootNorms μ L β τ h) := by
  let R : Set (ℝ × ℂ) := {p | p.1 ∈ Set.Icc μ L ∧ characteristic β τ h p.1 p.2 = 0}
  have hclosed : IsClosed R := by
    apply (isClosed_Icc.preimage continuous_fst).inter
    apply isClosed_eq _ continuous_const
    unfold characteristic queryPolynomial
    fun_prop
  have hcompact : IsCompact R := by
    apply (isCompact_Icc.prod (isCompact_closedBall (0 : ℂ) 1)).of_isClosed_subset hclosed
    intro p hp
    exact ⟨hp.1, by simpa using (hstable p.1 hp.1 p.2 hp.2).le⟩
  have himage : (fun p : ℝ × ℂ => ‖p.2‖) '' R = rootNorms μ L β τ h := by
    ext r
    constructor
    · rintro ⟨⟨lam, z⟩, hp, rfl⟩
      exact ⟨lam, hp.1, z, hp.2, rfl⟩
    · rintro ⟨lam, hlam, z, hz, rfl⟩
      exact ⟨(lam, z), ⟨hlam, hz⟩, rfl⟩
  rw [← himage]
  exact hcompact.image (continuous_norm.comp continuous_snd)

theorem quadraticRate_isGreatest {μ L β τ h : ℝ} (hμL : μ ≤ L)
    (hstable : Stable μ L β τ h) :
    IsGreatest (rootNorms μ L β τ h) (quadraticRate μ L β τ h) := by
  obtain ⟨r, hr⟩ := (isCompact_rootNorms_of_stable hstable).exists_isGreatest
    (rootNorms_nonempty hμL β τ h)
  simpa only [quadraticRate, hr.csSup_eq] using hr

theorem quadraticRate_nonneg {μ L β τ h : ℝ} (hμL : μ ≤ L)
    (hstable : Stable μ L β τ h) : 0 ≤ quadraticRate μ L β τ h := by
  obtain ⟨lam, _, z, _, he⟩ := (quadraticRate_isGreatest hμL hstable).1
  rw [he]
  exact norm_nonneg z

theorem quadraticRate_lt_one {μ L β τ h : ℝ} (hμL : μ ≤ L)
    (hstable : Stable μ L β τ h) : quadraticRate μ L β τ h < 1 := by
  obtain ⟨lam, hlam, z, hz, he⟩ := (quadraticRate_isGreatest hμL hstable).1
  rw [he]
  exact hstable lam hlam z hz

theorem root_norm_le_rate {μ L β τ h lam : ℝ} (hμL : μ ≤ L)
    (hstable : Stable μ L β τ h) (hlam : lam ∈ Set.Icc μ L) {z : ℂ}
    (hz : characteristic β τ h lam z = 0) : ‖z‖ ≤ quadraticRate μ L β τ h :=
  (quadraticRate_isGreatest hμL hstable).2 ⟨lam, hlam, z, hz, rfl⟩

theorem quadraticRate_tau_zero (μ L β h : ℝ) :
    quadraticRate μ L β 0 h = polyak.Dynamics.quadraticRate μ L h β := by
  unfold quadraticRate polyak.Dynamics.quadraticRate
  congr 1
  ext r
  simp only [rootNorms, polyak.Dynamics.quadraticRootNorms, characteristic_eq, S, Q,
    add_zero, mul_one, mul_zero, sub_zero]

end nesterov.Quadratic
