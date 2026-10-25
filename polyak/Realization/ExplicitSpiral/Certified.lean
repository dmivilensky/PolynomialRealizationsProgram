import polyak.Realization.ExplicitSpiral.AllIndices
import polyak.Certificates.Startup.Signs

/-!
Article: the complete finite-to-infinite certificate for the Y=2 initialization.
Use: every positive master root with 0<q<1 satisfies every exceptional pair.
-/
namespace polyak.Realization.ExplicitSpiral
noncomputable section
open polyak.Certificates.Startup LeanCert.Core

/-- Article: both disk signs for the actual lower slack. -/
theorem disk_certified_lower {r q : ℝ} (hr : 0<r) (hq : 0<q) (hq1 : q<1)
    (hF : Spiral.spiralPolynomial r q=0) (hlo : 33/100≤r) (hhi : r≤1)
    (k : ℕ) (hk : 1≤k) : 0 < initializedPairSlack r q (-1) k := by
  have hI : r∈Check00.interval := by
    norm_num [Check00.interval,IntervalRat.mem_def]
    exact ⟨hlo,hhi⟩
  apply disk_initialized_pair_pos hr hhi hq hq1 hF (by norm_num) _ _ k hk
  · have hh := Signs.sign00 hr hq hI hF
    nlinarith
  · have hh := Signs.sign01 hr hq hI hF
    norm_num at hh
    nlinarith

/-- Article: the three source quadratics for the actual lower slack. -/
theorem phase_certified_lower {r q : ℝ} (hq : 0<q) (hq1 : q<1)
    (hF : Spiral.spiralPolynomial r q=0) (hlo : 1≤r) (hhi : r≤6/5)
    (k : ℕ) (hk : 1≤k) : 0 < initializedPairSlack r q (-1) k := by
  have hr : 0<r := by linarith
  have hI : r∈Check02.interval := by
    norm_num [Check02.interval,IntervalRat.mem_def]
    exact ⟨hlo,hhi⟩
  apply phase_initialized_pair_pos hlo hq hq1 hF _ _ _ k hk
  · have hh := Signs.sign02 hr hq hI hF
    norm_num at hh
    nlinarith
  · have hh := Signs.sign03 hr hq hI hF
    norm_num at hh
    nlinarith
  · intro a ha
    have ha' : a≤2 := by omega
    interval_cases a

    · have hp := Signs.sign04 hr hq hI hF
      have hd := Signs.sign05 hr hq hI hF
      norm_num at hd
      exact ⟨by nlinarith,Or.inl (by nlinarith)⟩
    · have hp := Signs.sign06 hr hq hI hF
      have hd := Signs.sign07 hr hq hI hF
      norm_num at hd
      exact ⟨by nlinarith,Or.inl (by nlinarith)⟩
    · have hp := Signs.sign08 hr hq hI hF
      have hd := Signs.sign09 hr hq hI hF
      norm_num at hd
      exact ⟨by nlinarith,Or.inr (by nlinarith)⟩

/-- Article: all tail indices of the actual lower slack. -/
theorem tail_certified_lower {r q : ℝ} (hq : 0<q) (hq1 : q<1)
    (hF : Spiral.spiralPolynomial r q=0) (hlo : 6/5≤r) (hhi : r≤1713/1000)
    (k : ℕ) (hk : 10≤k) : 0 < initializedPairSlack r q (-1) k := by
  have hr : 0<r := by linarith
  have hI : r∈Check10.interval := by
    norm_num [Check10.interval,IntervalRat.mem_def]
    exact ⟨hlo,hhi⟩
  apply tail_initialized_pair_pos (by linarith) hq hq1 hF (by norm_num) _ _ _ k hk
  · have hh := Signs.sign10 hr hq hI hF
    norm_num at hh
    nlinarith
  · have hh := Signs.sign11 hr hq hI hF
    nlinarith
  · have hh := Signs.sign12 hr hq hI hF
    norm_num at hh
    nlinarith

/-- Article: the first nine actual lower slacks in the large-growth interval. -/
theorem finite_certified_lower {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hF : Spiral.spiralPolynomial r q=0) (hlo : 6/5≤r) (hhi : r≤1713/1000)
    (k : ℕ) (hk : 1≤k) (hk9 : k≤9) : 0 < initializedPairSlack r q (-1) k := by
  rw [initializedPairSlack_eq_source hr hq]
  have hI : r∈Check10.interval := by
    norm_num [Check10.interval,IntervalRat.mem_def]
    exact ⟨hlo,hhi⟩
  interval_cases k

  · have hh := Signs.sign26 hr hq hI hF
    nlinarith
  · have hh := Signs.sign28 hr hq hI hF
    nlinarith
  · have hh := Signs.sign30 hr hq hI hF
    nlinarith
  · have hh := Signs.sign32 hr hq hI hF
    nlinarith
  · have hh := Signs.sign34 hr hq hI hF
    nlinarith
  · have hh := Signs.sign36 hr hq hI hF
    nlinarith
  · have hh := Signs.sign38 hr hq hI hF
    nlinarith
  · have hh := Signs.sign40 hr hq hI hF
    nlinarith
  · have hh := Signs.sign42 hr hq hI hF
    nlinarith
/-- Article: both disk signs for the actual upper slack. -/
theorem disk_certified_upper {r q : ℝ} (hr : 0<r) (hq : 0<q) (hq1 : q<1)
    (hF : Spiral.spiralPolynomial r q=0) (hlo : 33/100≤r) (hhi : r≤1)
    (k : ℕ) (hk : 1≤k) : 0 < initializedPairSlack r q (1) k := by
  have hI : r∈Check00.interval := by
    norm_num [Check00.interval,IntervalRat.mem_def]
    exact ⟨hlo,hhi⟩
  apply disk_initialized_pair_pos hr hhi hq hq1 hF (by norm_num) _ _ k hk
  · have hh := Signs.sign13 hr hq hI hF
    nlinarith
  · have hh := Signs.sign14 hr hq hI hF
    norm_num at hh
    nlinarith

/-- Article: the three source quadratics for the actual upper slack. -/
theorem phase_certified_upper {r q : ℝ} (hq : 0<q) (hq1 : q<1)
    (hF : Spiral.spiralPolynomial r q=0) (hlo : 1≤r) (hhi : r≤6/5)
    (k : ℕ) (hk : 1≤k) : 0 < initializedPairSlack r q (1) k := by
  have hr : 0<r := by linarith
  have hI : r∈Check02.interval := by
    norm_num [Check02.interval,IntervalRat.mem_def]
    exact ⟨hlo,hhi⟩
  apply phase_initialized_pair_pos hlo hq hq1 hF _ _ _ k hk
  · have hh := Signs.sign15 hr hq hI hF
    norm_num at hh
    nlinarith
  · have hh := Signs.sign16 hr hq hI hF
    norm_num at hh
    nlinarith
  · intro a ha
    have ha' : a≤2 := by omega
    interval_cases a

    · have hp := Signs.sign17 hr hq hI hF
      have hd := Signs.sign18 hr hq hI hF
      norm_num at hd
      exact ⟨by nlinarith,Or.inr (by nlinarith)⟩
    · have hp := Signs.sign19 hr hq hI hF
      have hd := Signs.sign20 hr hq hI hF
      norm_num at hd
      exact ⟨by nlinarith,Or.inr (by nlinarith)⟩
    · have hp := Signs.sign21 hr hq hI hF
      have hd := Signs.sign22 hr hq hI hF
      norm_num at hd
      exact ⟨by nlinarith,Or.inl (by nlinarith)⟩

/-- Article: all tail indices of the actual upper slack. -/
theorem tail_certified_upper {r q : ℝ} (hq : 0<q) (hq1 : q<1)
    (hF : Spiral.spiralPolynomial r q=0) (hlo : 6/5≤r) (hhi : r≤1713/1000)
    (k : ℕ) (hk : 10≤k) : 0 < initializedPairSlack r q (1) k := by
  have hr : 0<r := by linarith
  have hI : r∈Check10.interval := by
    norm_num [Check10.interval,IntervalRat.mem_def]
    exact ⟨hlo,hhi⟩
  apply tail_initialized_pair_pos (by linarith) hq hq1 hF (by norm_num) _ _ _ k hk
  · have hh := Signs.sign23 hr hq hI hF
    norm_num at hh
    nlinarith
  · have hh := Signs.sign24 hr hq hI hF
    nlinarith
  · have hh := Signs.sign25 hr hq hI hF
    norm_num at hh
    nlinarith

/-- Article: the first nine actual upper slacks in the large-growth interval. -/
theorem finite_certified_upper {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hF : Spiral.spiralPolynomial r q=0) (hlo : 6/5≤r) (hhi : r≤1713/1000)
    (k : ℕ) (hk : 1≤k) (hk9 : k≤9) : 0 < initializedPairSlack r q (1) k := by
  rw [initializedPairSlack_eq_source hr hq]
  have hI : r∈Check10.interval := by
    norm_num [Check10.interval,IntervalRat.mem_def]
    exact ⟨hlo,hhi⟩
  interval_cases k

  · have hh := Signs.sign27 hr hq hI hF
    nlinarith
  · have hh := Signs.sign29 hr hq hI hF
    nlinarith
  · have hh := Signs.sign31 hr hq hI hF
    nlinarith
  · have hh := Signs.sign33 hr hq hI hF
    nlinarith
  · have hh := Signs.sign35 hr hq hI hF
    nlinarith
  · have hh := Signs.sign37 hr hq hI hF
    nlinarith
  · have hh := Signs.sign39 hr hq hI hF
    nlinarith
  · have hh := Signs.sign41 hr hq hI hF
    nlinarith
  · have hh := Signs.sign43 hr hq hI hF
    nlinarith

/-- Article: every initialized interpolation pair, for every κ>1 and every horizon. -/
theorem certified_initial_pair_pos {r q : ℝ} (hr : 0<r) (hq : 0<q) (hq1 : q<1)
    (hF : Spiral.spiralPolynomial r q=0) (δ : ℝ) (hδ : δ=1 ∨ δ= -1)
    (k : ℕ) (hk : 1≤k) : 0 < initializedPairSlack r q δ k := by
  by_cases hq5 : q≤1/5
  · exact small_initialized_pair_pos hr hq hq5 hF δ hδ k hk
  · have hlo := root_gt_lower hr hq hq1 (by linarith) hF
    have hhi := root_lt_upper hr hq hq1 hF
    by_cases hr1 : r≤1
    · rcases hδ with rfl | rfl
      · exact disk_certified_upper hr hq hq1 hF hlo.le hr1 k hk
      · exact disk_certified_lower hr hq hq1 hF hlo.le hr1 k hk
    · by_cases hr6 : r≤6/5
      · rcases hδ with rfl | rfl
        · exact phase_certified_upper hq hq1 hF (by linarith) hr6 k hk
        · exact phase_certified_lower hq hq1 hF (by linarith) hr6 k hk
      · by_cases hkt : 10≤k
        · rcases hδ with rfl | rfl
          · exact tail_certified_upper hq hq1 hF (by linarith) hhi.le k hkt
          · exact tail_certified_lower hq hq1 hF (by linarith) hhi.le k hkt
        · rcases hδ with rfl | rfl
          · exact finite_certified_upper hr hq hF (by linarith) hhi.le k hk (by omega)
          · exact finite_certified_lower hr hq hF (by linarith) hhi.le k hk (by omega)

end
end polyak.Realization.ExplicitSpiral
