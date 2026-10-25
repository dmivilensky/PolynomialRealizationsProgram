import polyak.FareyPlateau.FanAnalysis.PenaltyCoefficient
import polyak.FareyPlateau.Plateau.SingletonPeriod

/-! The sharp nondivisible-period penalty, in the epsilon/cutoff form
equivalent to the article's 1+o(1) lower bound. Every competing grid is included. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis.Actual
open General Levels ModeLocking Set MeasureTheory Metric
open scoped BigOperators
variable {q : Tuning} {j k : ℕ} (A : Edge.AdjacentData q j k)

theorem nondiv_grid_distance {M : ℕ} (hM : 3≤M) (hdiv : ¬k∣M)
    {ω : Frequency} (hω : ω∈periodicGrid M) :
    2*Real.pi/((k:ℝ)*M)≤|(ω:ℝ)-(A.frequency:ℝ)| := by
  have hk : 0<k := by have := A.period_ge; omega
  have hne : ω≠A.frequency := by
    intro he
    apply hdiv
    apply rational_atom_period hk A.numerator_lt.le A.inverse A.inverse_mod
    simpa only [he,Edge.AdjacentData.frequency] using hω
  have hh := Localization.rational_grid_distance (by omega : 0<M) hk hω
    (Edge.atom_grid A.numerator_pos hk A.numerator_lt.le) (by
      simpa only [Edge.AdjacentData.frequency] using hne)
  have hp : (0:ℝ)<Nat.lcm M k := by
    exact_mod_cast Nat.lcm_pos (by omega : 0<M) hk
  have hmul : (Nat.lcm M k:ℝ)≤(k:ℝ)*M := by
    exact_mod_cast (show Nat.lcm M k≤k*M by
      simpa only [Nat.mul_comm] using Nat.lcm_le_mul (by omega : 0<M) hk)
  exact (div_le_div_of_nonneg_left (by positivity : 0≤2*Real.pi) hp hmul).trans hh

theorem nondiv_period_penalty
    (hstrict : ∀x : ℝ,0<x → x≤Real.pi → x≠(A.frequency:ℝ) → 0<A.function x)
    (hcurv : 0<deriv^[2] A.function A.frequency)
    (hend : 0<deriv^[2] A.function 0)
    (ε : ℝ) (hε : 0<ε) :
    ∃M₀ : ℕ,∀M : ℕ,3≤M → M₀≤M → ¬k∣M →
      (deriv^[2] A.function A.frequency/(2*(Real.sin (Real.pi/k))^3))*
        (2*Real.pi/((k:ℝ)*M))^2*(1-ε)≤Threshold.sigmaPeriodic q M-A.edgeShift := by
  let C := A.certificate hstrict hcurv hend
  let D := C.regularData
  let v := Localization.minimalLockingCoefficient D
  have hv : 0<v := Localization.minimalLockingCoefficient_pos D
  have heq : v=deriv^[2] A.function A.frequency/(2*(Real.sin (Real.pi/k))^3) :=
    adjacent_locking_coefficient A hstrict hcurv hend
  by_cases hε1 : ε<1
  · obtain ⟨r,hr,hpenalty⟩ := Localization.regular_sharp_potential_penalty D (v*ε)
      (mul_pos hv hε) (by dsimp [v]; nlinarith)
    obtain ⟨M₀,hM₀⟩ := exists_nat_gt (2*Real.pi/((k:ℝ)*r))
    refine ⟨M₀,?_⟩
    intro M hM hMM₀ hdiv
    have hk : (0:ℝ)<k := by exact_mod_cast (show 0<k by have := A.period_ge; omega)
    have hMr : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
    let d : ℝ := 2*Real.pi/((k:ℝ)*M)
    have hd : 0<d := by dsimp [d]; positivity
    have hdr : d<r := by
      have hh : 2*Real.pi/((k:ℝ)*r)<(M:ℝ) := hM₀.trans_le (by exact_mod_cast hMM₀)
      have hh' := (div_lt_iff₀ (mul_pos hk hr)).mp hh
      apply (div_lt_iff₀ (mul_pos hk hMr)).mpr
      nlinarith
    obtain ⟨w,hw,hcar⟩ := Threshold.sigmaPeriodic_feasible q hM
    have hsupport : w.support⊆periodicGrid M :=
      w.support_subset_of_isClosed (periodicGrid_finite (by omega : 0<M)).isClosed hcar
    have hZ : Localization.regularSupport D={(A.frequency:ℝ)} := by
      change Finset.univ.image (fun _ : Fin 1=>(A.frequency:ℝ))={(A.frequency:ℝ)}
      simp
    have hbound := Localization.support_potential_penalty D (Threshold.sigmaPeriodic q M)
      ((v-v*ε)*d^2) hw (by
        intro ω hω hωint
        have hdist : d ≤ infDist (ω:ℝ) (Localization.regularSupport D:Set ℝ) := by
          rw [hZ,Finset.coe_singleton,infDist_singleton,Real.dist_eq]
          exact nondiv_grid_distance A hM hdiv (hsupport hω)
        have hh := hpenalty d hd hdr (ω:ℝ) hωint hdist
        rwa [Localization.extendedPotential_actual D ω] at hh)
    rw [←heq]
    convert hbound using 1
    ring
  · refine ⟨0,?_⟩
    intro M hM _ _
    have hnonneg : 0≤Threshold.sigmaPeriodic q M-A.edgeShift := by
      rw [←D.sigma_eq]
      exact sub_nonneg.mpr (Threshold.sigma_le_sigmaPeriodic q hM)
    rw [←heq]
    exact (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hv.le (sq_nonneg _))
      (by linarith)).trans hnonneg

end polyak.FareyPlateau.FanAnalysis.Actual
