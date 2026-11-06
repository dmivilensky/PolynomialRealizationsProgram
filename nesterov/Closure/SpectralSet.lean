import nesterov.Spectral.Realization
import nesterov.Duality.Persistence
import nesterov.Rates.QuadraticMaximum
import polyak.Waves.Finite

/-! The full set of feasible exponents of an arbitrary stationary method.
The upper bound uses the actual realized trajectory, and quadratic roots give
actual feasible spectra without a coprimality assumption. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal
namespace nesterov.Closure
open Spectral

def spectralSet (M : StationaryMethod) (μ L : ℝ) : Set ℝ :=
  {t | ∃ ν C, Feasible (M.symbolPair μ L t) t ν C}

theorem isClosed_spectralSet (M : StationaryMethod) (μ L : ℝ) :
    IsClosed (spectralSet M μ L) := by
  exact nesterov.Duality.isClosed_exists_feasible
    (ContinuousMap.continuous_of_continuous_uncurry _ (M.continuous_symbolPair_u μ L))
    (ContinuousMap.continuous_of_continuous_uncurry _ (M.continuous_symbolPair_p μ L)) continuous_id

theorem spectralSet_le_exponent (M : StationaryMethod) {μ L : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) {t : ℝ} (h : t ∈ spectralSet M μ L) :
    t ≤ Rates.exponent M μ L := by
  obtain ⟨ν, C, h⟩ := h
  exact Real.exp_le_exp.mp (h.exp_le_rate hμ hμL)

theorem bddAbove_spectralSet (M : StationaryMethod) {μ L : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) : BddAbove (spectralSet M μ L) :=
  ⟨Rates.exponent M μ L, fun _ h => spectralSet_le_exponent M hμ hμL h⟩

/-- A real scalar relation p=du, |d|≤1, supplies every lag at a single frequency. -/
theorem feasible_singleton_of_real_mul (a : SymbolPair) (t : ℝ) (c : Frequency)
    (d : ℝ) (hd : |d| ≤ 1) (hp : a.p c = (d : ℂ) * a.u c) :
    ∃ ν : Spectrum, Feasible a t ν 0 := by
  let w : Fin 1 → ℝ≥0 := fun _ => 1
  let cs : Fin 1 → Frequency := fun _ => c
  have hw : ∑ j, w j = 1 := by simp [w]
  let ν := polyak.Waves.finiteSpectrum w cs hw
  have hg : 0 ≤ g a c := by
    rw [g, hp, Complex.normSq_mul, Complex.normSq_ofReal]
    have hs := (sq_le_one_iff_abs_le_one d).mpr hd
    nlinarith [Complex.normSq_nonneg (a.u c)]
  have hsk : skew a c = 0 := by
    simp only [skew, hp, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have hmeanG : meanG ν a = g a c := by
    simp [meanG, ν, polyak.Waves.finiteSpectrum_integral, w, cs]
  have hmeanA (n : ℕ) : meanA ν a t n = lagA a t n c := by
    simp [meanA, ν, polyak.Waves.finiteSpectrum_integral, w, cs]
  have hmeanB (n : ℕ) : meanB ν a n = 0 := by
    simp [meanB, ν, polyak.Waves.finiteSpectrum_integral, w, cs, lagB, hsk]
  refine ⟨ν, ?_, fun n _ => ?_⟩
  · simpa only [abs_zero, hmeanG] using hg
  · rw [hmeanA, hmeanB]
    have hh : 0 ≤ lagA a t n c := mul_nonneg hg
      (sub_nonneg.mpr ((Real.cos_le_one _).trans (Real.one_le_cosh _)))
    simpa using And.intro hh hh

private theorem root_log_mem_upper (M : StationaryMethod) {μ L lam : ℝ}
    (hμL : μ < L) (hlam : lam ∈ Set.Icc μ L) {z : ℂ} (hz0 : z ≠ 0)
    (hz : M.characteristic lam z = 0) (him : 0 ≤ z.im) :
    Real.log ‖z‖ ∈ spectralSet M μ L := by
  let c : Frequency := ⟨Real.cos z.arg, Real.neg_one_le_cos _, Real.cos_le_one _⟩
  let d : ℝ := (L+μ-2*lam)/(L-μ)
  have hd : |d| ≤ 1 := by
    rw [abs_le]
    constructor
    · exact (le_div_iff₀ (sub_pos.mpr hμL)).mpr (by linarith [hlam.2])
    · exact (div_le_iff₀ (sub_pos.mpr hμL)).mpr (by linarith [hlam.1])
  have har : Real.arccos (c : ℝ) = z.arg :=
    Real.arccos_cos (Complex.arg_nonneg_iff.mpr him) (Complex.arg_le_pi _)
  have hwave : polyak.Waves.z (Real.log ‖z‖) (Real.arccos c) = z := by
    rw [har]
    exact Complex.exp_log hz0
  have hchar : (M.recurrencePolynomial.map Complex.ofRealHom).eval z =
      (lam : ℂ) * (M.queryPolynomial.map Complex.ofRealHom).eval z := by
    have hh := hz
    rw [M.characteristic_eq_polynomial_eval] at hh
    simpa only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, sub_eq_zero] using hh
  have hp : (M.symbolPair μ L (Real.log ‖z‖)).p c =
      (d : ℂ) * (M.symbolPair μ L (Real.log ‖z‖)).u c := by
    rw [M.symbolPair_p, M.symbolPair_u, hwave, M.normalizedPolynomial_complex_eval, hchar]
    have hd' : ((L+μ)/(L-μ) : ℝ) - 2/(L-μ)*lam = d := by dsimp [d]; ring
    have he := congrArg (fun r : ℝ => (r : ℂ)) hd'
    push_cast at he
    push_cast
    linear_combination he * (M.queryPolynomial.map Complex.ofRealHom).eval z
  obtain ⟨ν, hν⟩ := feasible_singleton_of_real_mul (M.symbolPair μ L (Real.log ‖z‖))
    (Real.log ‖z‖) c d hd hp
  exact ⟨ν, 0, hν⟩

/-- Every nonzero characteristic root yields a literal one-atom feasible pair. -/
theorem characteristicRoot_log_mem (M : StationaryMethod) {μ L lam : ℝ}
    (hμL : μ < L) (hlam : lam ∈ Set.Icc μ L) {z : ℂ} (hz0 : z ≠ 0)
    (hz : M.characteristic lam z = 0) : Real.log ‖z‖ ∈ spectralSet M μ L := by
  by_cases hi : 0 ≤ z.im
  · exact root_log_mem_upper M hμL hlam hz0 hz hi
  · have hz' : M.characteristic lam (starRingEnd ℂ z) = 0 := by
      have hh := congrArg (starRingEnd ℂ) hz
      simpa only [StationaryMethod.characteristic, map_sub, map_mul, map_pow,
        map_sum, map_zero, Complex.conj_ofReal] using hh
    have hh := root_log_mem_upper M hμL hlam
      (star_ne_zero.mpr hz0) hz' (by simpa using (lt_of_not_ge hi).le)
    simpa only [map_star, norm_star] using hh

theorem spectralSet_nonempty (M : StationaryMethod) {μ L : ℝ} (hμL : μ < L) :
    (spectralSet M μ L).Nonempty := by
  obtain ⟨lam, hlam, z, hz0, hz⟩ := M.exists_nonzero_characteristic_root hμL
  exact ⟨_, characteristicRoot_log_mem M hμL hlam hz0 hz⟩

/-- Theorem A(a): the spectral program has an attained finite upper endpoint. -/
theorem spectralSet_has_maximum (M : StationaryMethod) {μ L : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) : ∃ T, IsGreatest (spectralSet M μ L) T := by
  refine ⟨sSup (spectralSet M μ L),
    (isClosed_spectralSet M μ L).csSup_mem (spectralSet_nonempty M hμL)
      (bddAbove_spectralSet M hμ hμL), ?_⟩
  intro t ht
  exact le_csSup (bddAbove_spectralSet M hμ hμL) ht

/-- The article's maximal feasible exponent. -/
def T (M : StationaryMethod) (μ L : ℝ) : ℝ := sSup (spectralSet M μ L)

theorem T_isGreatest (M : StationaryMethod) {μ L : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) : IsGreatest (spectralSet M μ L) (T M μ L) := by
  obtain ⟨T', hT⟩ := spectralSet_has_maximum M hμ hμL
  simpa only [T, hT.csSup_eq] using hT

theorem T_mem (M : StationaryMethod) {μ L : ℝ} (hμ : 0 < μ) (hμL : μ < L) :
    ∃ ν C, Feasible (M.symbolPair μ L (T M μ L)) (T M μ L) ν C :=
  (T_isGreatest M hμ hμL).1

/-- Theorem A(a)'s quadratic lower endpoint is included and lies below T. -/
theorem log_quadraticRate_mem (M : StationaryMethod) {μ L : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) :
    Real.log (Rates.quadraticRate M μ L) ∈ spectralSet M μ L := by
  obtain ⟨lam, hlam, z, hz, hr⟩ := (Rates.quadraticRate_isGreatest M hμ hμL).1
  have hz0 : z ≠ 0 := by
    apply norm_pos_iff.mp
    rw [← hr]
    exact Rates.quadraticRate_pos M hμ hμL
  rw [hr]
  exact characteristicRoot_log_mem M hμL hlam hz0 hz

theorem log_quadraticRate_le_T (M : StationaryMethod) {μ L : ℝ}
    (hμ : 0 < μ) (hμL : μ < L) :
    Real.log (Rates.quadraticRate M μ L) ≤ T M μ L :=
  (T_isGreatest M hμ hμL).2 (log_quadraticRate_mem M hμ hμL)

end nesterov.Closure
