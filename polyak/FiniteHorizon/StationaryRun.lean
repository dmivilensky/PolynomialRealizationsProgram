import polyak.FiniteHorizon.StationaryWindow
import polyak.Growth.HorizonExtension
import polyak.Duality.FiniteMemory

/-!
Article: Appendix C, stationary trajectories in the finite-memory class.
Use: every finite spectral feasibility pair defines one genuine infinite H-table
in its real L² Hilbert space, including arbitrary non-atomic spectra.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Interpolation Spectral Waves Duality

theorem finiteMixture_star_bound {ν : Spectrum} {m : C(Frequency, ℂ)} {C t : ℝ} {H : ℕ}
    (h : FiniteFeasible m t H ν C) (j : ℕ) :
    |datumT (mixturePosition ν t) (mixtureGradient ν m t) (mixtureValue ν m C t)
      none (some j)| ≤ datumR (mixturePosition ν t) (mixtureGradient ν m t) none (some j) := by
  rw [abs_le_iff_signed_slacks]
  have hC := abs_le.mp h.1
  have hpos := mixture_star_slack ν m C t 1 j
  have hneg := mixture_star_slack ν m C t (-1) j
  simp only [one_mul, neg_one_mul] at hpos hneg
  constructor
  · rw [hpos]
    exact mul_nonneg (by positivity) (by linarith)
  · have he : datumR (mixturePosition ν t) (mixtureGradient ν m t) none (some j) -
        datumT (mixturePosition ν t) (mixtureGradient ν m t) (mixtureValue ν m C t)
          none (some j) = (1 / 4 : ℝ) * Real.exp (2 * j * t) * (spectrumG ν m - C) := by
      linarith [hneg]
    rw [he]
    exact mul_nonneg (by positivity) (by linarith)

theorem finiteMixture_lag_bound {ν : Spectrum} {m : C(Frequency, ℂ)} {C t : ℝ} {H : ℕ}
    (h : FiniteFeasible m t H ν C) (j n : ℕ) (hnH : n≤H) :
    |datumT (mixturePosition ν t) (mixtureGradient ν m t) (mixtureValue ν m C t)
      (some j) (some (j + n))| ≤
      datumR (mixturePosition ν t) (mixtureGradient ν m t) (some j) (some (j + n)) := by
  by_cases hn : n = 0
  · subst n
    simp [datumT, datumR]
  · have hn' : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    obtain ⟨hl, hu⟩ := h.2 n hn' hnH
    rw [abs_le_iff_signed_slacks]
    have hpos := mixture_slack ν m C t 1 j n
    have hneg := mixture_slack ν m C t (-1) j n
    simp only [one_mul, neg_one_mul, sub_neg_eq_add] at hpos hneg
    constructor
    · rw [hpos]
      exact mul_nonneg (by positivity) hl
    · have he : datumR (mixturePosition ν t) (mixtureGradient ν m t)
          (some j) (some (j + n)) - datumT (mixturePosition ν t) (mixtureGradient ν m t)
            (mixtureValue ν m C t) (some j) (some (j + n)) =
          (1 / 2 : ℝ) * Real.exp ((2 * j + n) * t) *
            (spectrumA ν m t n + spectrumB ν m n - C * Real.sinh (n * t)) := by
        linarith [hneg]
      rw [he]
      exact mul_nonneg (by positivity) hu

def stationaryHRun {A B β t C : ℝ} {H : ℕ} (hB : B≠0) (ν : Spectrum)
    (h : FiniteFeasible (multiplierMap A B β t) t H ν C) : HRun (WaveSpace ν) A B β H where
  x k:=mixturePosition ν t (some k)
  σ k:=mixtureGradient ν (multiplierMap A B β t) t (some k)
  value k:=mixtureValue ν (multiplierMap A B β t) C t (some k)
  interpolation i _ j _ hij:=by
    change |datumT (mixturePosition ν t) (mixtureGradient ν (multiplierMap A B β t) t)
      (mixtureValue ν (multiplierMap A B β t) C t) (some i) (some j)|≤
      datumR (mixturePosition ν t) (mixtureGradient ν (multiplierMap A B β t) t) (some i) (some j)
    by_cases hle : i≤j
    · have hlag : j-i≤H:=by unfold Nat.dist at hij; omega
      simpa only [Nat.add_sub_of_le hle] using finiteMixture_lag_bound h i (j-i) hlag
    · rw [pair_bound_reverse]
      have hle' : j ≤ i :=by omega
      have hlag : i-j≤H:=by unfold Nat.dist at hij; omega
      simpa only [Nat.add_sub_of_le hle'] using finiteMixture_lag_bound h j (i-j) hlag
  origin i _:=by
    have hs:=finiteMixture_star_bound h i
    simpa only [datumT,datumR,mixturePosition_none,mixtureGradient_none,mixtureValue_none,
      sub_zero,zero_add] using hs
  recurrence k:=mixture_recurrence ν A B β t hB k

end polyak.FiniteHorizon
