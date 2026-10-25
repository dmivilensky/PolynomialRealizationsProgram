import polyak.Spectral.ActualBoundary
import polyak.Spectral.FiniteSupport
import polyak.Spectral.Atomic
import polyak.Spectral.StrictMinimizer
import polyak.Realization.Rate

/-!
Article: Theorem spectral, finite optimal spectra and the original from-rest rate.
Use: every noncritical optimal measure has a common finite interior carrier,
strict minimizer reserve, and only finitely many active lag constraints.
Proof: the attained positive-twist boundary confines every optimal measure to
one finite zero set; its exact atomic decomposition permits the original startup
realization.  The critical three-cycle supplies the remaining zero-exponent case.
-/

noncomputable section
open MeasureTheory

namespace polyak.Spectral

/-- Article: the maximum in the source definition of T is attained, with its
absolute-twist criterion rather than an auxiliary feasibility predicate. -/
theorem isGreatest_T_twist {q : ℝ} (hq : 0 < q) :
    IsGreatest {t : ℝ | |t - Real.log q| ≤ V t} (T q) := by
  have he : {t : ℝ | |t - Real.log q| ≤ V t} = exponents q := by
    ext t
    exact (mem_twists_iff (t - Real.log q) t).symm
  rw [he]
  exact isGreatest_T hq

/-- Article: one finite interior carrier contains every actual optimal spectrum.
The carrier is chosen independently of the optimal measure and its value constant. -/
theorem exists_actual_optimal_carrier {q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (ht : T q ≠ 0) :
    ∃ F : Set Frequency, F.Finite ∧ (∀ c ∈ F, -1 < (c : ℝ) ∧ (c : ℝ) < 1) ∧
      ∀ (ν : Spectrum) (C : ℝ), Feasible (T q - Real.log q) (T q) ν C →
        (ν : Measure Frequency) Fᶜ = 0 := by
  have hs : 0 < |T q| := abs_pos.mpr ht
  have hV : 0 < V |T q| := by
    rw [← actual_boundary_abs hq hq1 ht]
    exact actual_twist_pos hq hq1
  obtain ⟨F,hF,hFi,hcarrier⟩ := exists_finite_boundary_carrier hs hV
  refine ⟨F,hF,hFi,fun ν C h => ?_⟩
  have hf : ∃ D : ℝ, Feasible (V |T q|) |T q| ν D := by
    rcases le_total 0 (T q) with hp | hn
    · refine ⟨C,?_⟩
      rw [← actual_boundary_abs hq hq1 ht,abs_of_nonneg hp]
      exact h
    · refine ⟨-C,?_⟩
      rw [← actual_boundary_abs hq hq1 ht,abs_of_nonpos hn]
      exact (feasible_neg_t_iff (T q - Real.log q) (T q) C ν).mpr h
  obtain ⟨D,hD⟩ := hf
  exact hcarrier ν D hD

/-- Article: every noncritical optimal spectrum has strict minimizer reserve.
No atomicity or strictness hypothesis is imposed on the input measure. -/
theorem actual_optimal_strict_minimizer {q C : ℝ} {ν : Spectrum}
    (hq : 0 < q) (hq1 : q < 1) (ht : T q ≠ 0)
    (h : Feasible (T q - Real.log q) (T q) ν C) :
    |C| < meanG ν (Real.sinh (T q - Real.log q)) := by
  classical
  obtain ⟨F,hF,hFi,hcarrier⟩ := exists_actual_optimal_carrier hq hq1 ht
  let : Fintype F := hF.fintype
  obtain ⟨w,hw,he⟩ := exists_finiteSpectrum_of_support ν (hcarrier ν C h)
  have hci : Function.Injective (fun j : F => j.val) := fun _ _ hij => Subtype.ext hij
  have hc : ∀ j : F, -1 < (j.val : ℝ) ∧ (j.val : ℝ) < 1 := fun j => hFi j.val j.property
  rw [← he] at h ⊢
  exact finite_feasible_strict_minimizer w (fun j => j.val) hw hci hc ht h

/-- Article: all sufficiently large lag constraints of any noncritical optimizer
are strictly inactive, in both orientations. -/
theorem actual_optimal_active_lags_bounded {q C : ℝ} {ν : Spectrum}
    (hq : 0 < q) (hq1 : q < 1) (ht : T q ≠ 0)
    (h : Feasible (T q - Real.log q) (T q) ν C) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      0 < meanA ν (Real.sinh (T q - Real.log q)) (T q) m -
        meanB ν (Real.sinh (T q - Real.log q)) m + C * Real.sinh (m * T q) ∧
      0 < meanA ν (Real.sinh (T q - Real.log q)) (T q) m +
        meanB ν (Real.sinh (T q - Real.log q)) m - C * Real.sinh (m * T q) := by
  have hstrict := actual_optimal_strict_minimizer hq hq1 ht h
  exact Filter.eventually_atTop.mp (Boundary.eventually_raw_lags_positive ν
    (Real.sinh (T q - Real.log q)) C (T q) hstrict ht)

/-- Article: any noncritical optimum supplies the lower rate for the original
Polyak iteration, including its prescribed zero initial impulse. -/
theorem exp_T_le_originalRate_of_ne_zero {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L)
    (ht : T (Dynamics.polyakQ μ L) ≠ 0) :
    Real.exp (T (Dynamics.polyakQ μ L)) ≤
      Dynamics.rate μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L) := by
  classical
  let q := Dynamics.polyakQ μ L
  have hq : 0 < q := Dynamics.polyakQ_pos hμ hL
  have hq1 : q < 1 := Dynamics.polyakQ_lt_one hμ hL
  obtain ⟨ν,C,h⟩ := T_mem hq
  obtain ⟨F,hF,_,hcarrier⟩ := exists_actual_optimal_carrier hq hq1 ht
  let : Fintype F := hF.fintype
  obtain ⟨w,hw,he⟩ := exists_finiteSpectrum_of_support ν (hcarrier ν C h)
  have hm := (actual_feasible_iff hq (T q) C ν).mpr h
  have hstrict := actual_optimal_strict_minimizer hq hq1 ht h
  have hg : Waves.spectrumG ν (Waves.multiplierMap 0 (2*q) (q^2) (T q)) =
      meanG ν (Real.sinh (T q - Real.log q)) := by
    rw [Waves.multiplierMap_polyak q (T q) hq,Waves.spectrumG_polyak]
  have hmix : Waves.MixtureFeasible (Waves.finiteSpectrum w (fun j => j.val) hw)
      (Waves.multiplierMap
        (Dynamics.normalizedA μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L))
        (Dynamics.normalizedB μ L (Dynamics.polyakAlpha μ L))
        (Dynamics.polyakBeta μ L) (T q)) C (T q) := by
    rw [he,Dynamics.polyak_normalizedA hμ hL,Dynamics.polyak_normalizedB hμ hL]
    exact hm
  have hgap : |C| < Waves.spectrumG (Waves.finiteSpectrum w (fun j => j.val) hw)
      (Waves.multiplierMap
        (Dynamics.normalizedA μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L))
        (Dynamics.normalizedB μ L (Dynamics.polyakAlpha μ L))
        (Dynamics.polyakBeta μ L) (T q)) := by
    rw [he,Dynamics.polyak_normalizedA hμ hL,Dynamics.polyak_normalizedB hμ hL]
    exact hg.symm ▸ hstrict
  exact Realization.exp_le_originalRate hμ hL (Dynamics.polyakAlpha_pos hμ hL)
    (Dynamics.polyakBeta_mem hμ hL).1 (Dynamics.polyakBeta_mem hμ hL).2
    (Dynamics.polyak_quadratic_condition hμ hL).2 w (fun j => j.val) hw hmix (fun _ => hgap)

/-- Article: the exact original worst-case Polyak rate, for every admissible
curvature pair.  The critical case is supplied by the actual three-cycle. -/
theorem originalRate_eq_exp_T {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    Dynamics.rate μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L) =
      Real.exp (T (Dynamics.polyakQ μ L)) := by
  by_cases ht : T (Dynamics.polyakQ μ L) = 0
  · rw [ht,Real.exp_zero]
    exact Threshold.original_polyakRate_critical hμ hL
      ((T_eq_zero_iff (Dynamics.polyakQ_pos hμ hL) (Dynamics.polyakQ_lt_one hμ hL)).mp ht)
  · exact le_antisymm (originalRate_le_exp_T hμ hL)
      (exp_T_le_originalRate_of_ne_zero hμ hL ht)

/-- Article: Theorem spectral, all assertions of the spectral rate theorem.
The optimal-measure assertions quantify over every feasible optimal measure;
no choice of a classified family or of an atomic optimizer is made. -/
theorem spectral_rate {μ L : ℝ} (hμ : 0 < μ) (hL : μ < L) :
    Dynamics.rate μ L (Dynamics.polyakAlpha μ L) (Dynamics.polyakBeta μ L) =
        Real.exp (T (Dynamics.polyakQ μ L)) ∧
    (∀ t : ℝ, V (-t) = V t) ∧
    (∀ t : ℝ, 0 ≤ V t ∧ V t ≤ Real.arsinh 1) ∧
    (∀ t : ℝ, twists t = Set.Icc (-V t) (V t)) ∧
    (T (Dynamics.polyakQ μ L) ≠ 0 →
      ∃ F : Set Frequency, F.Finite ∧ (∀ c ∈ F, -1 < (c : ℝ) ∧ (c : ℝ) < 1) ∧
        ∀ (ν : Spectrum) (C : ℝ),
          Feasible (T (Dynamics.polyakQ μ L) - Real.log (Dynamics.polyakQ μ L))
            (T (Dynamics.polyakQ μ L)) ν C →
          (ν : Measure Frequency) Fᶜ = 0 ∧
          |C| < meanG ν (Real.sinh
            (T (Dynamics.polyakQ μ L) - Real.log (Dynamics.polyakQ μ L))) ∧
          ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
            0 < meanA ν (Real.sinh
                (T (Dynamics.polyakQ μ L) - Real.log (Dynamics.polyakQ μ L)))
                (T (Dynamics.polyakQ μ L)) m -
              meanB ν (Real.sinh
                (T (Dynamics.polyakQ μ L) - Real.log (Dynamics.polyakQ μ L))) m +
              C * Real.sinh (m * T (Dynamics.polyakQ μ L)) ∧
            0 < meanA ν (Real.sinh
                (T (Dynamics.polyakQ μ L) - Real.log (Dynamics.polyakQ μ L)))
                (T (Dynamics.polyakQ μ L)) m +
              meanB ν (Real.sinh
                (T (Dynamics.polyakQ μ L) - Real.log (Dynamics.polyakQ μ L))) m -
              C * Real.sinh (m * T (Dynamics.polyakQ μ L))) := by
  refine ⟨originalRate_eq_exp_T hμ hL, V_even, fun t => ⟨V_nonneg t,V_le_arsinh_one t⟩,
    twists_eq_Icc, fun ht => ?_⟩
  have hq := Dynamics.polyakQ_pos hμ hL
  have hq1 := Dynamics.polyakQ_lt_one hμ hL
  obtain ⟨F,hF,hFi,hcarrier⟩ := exists_actual_optimal_carrier hq hq1 ht
  exact ⟨F,hF,hFi,fun ν C h => ⟨hcarrier ν C h,
    actual_optimal_strict_minimizer hq hq1 ht h,
    actual_optimal_active_lags_bounded hq hq1 ht h⟩⟩

end polyak.Spectral
