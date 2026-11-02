import krylov.Design.HyperbolicSeriesLimit
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Article: main_krylov, the lower Chebyshev majorant after thm:B and its proof
at the end of apC:sec:design.
Use: construct and characterize the unique genuine maximum of y*sech(y)
on the nonnegative half-line, without assuming an extremizer or stationarity.
Source: elementary hyperbolic differentiation, the intermediate value theorem,
and the mean value theorem in mathlib.
-/

namespace krylov.Design
noncomputable section
open Real Filter Set jacobi.Young
open scoped Topology

/-- The real profile whose lattice samples give the asymptotic lower majorant.
Article: main_krylov, the lower Chebyshev majorant after thm:B. -/
def sechProfile (y : ℝ) : ℝ := y * sech y

/-- The actual hyperbolic secant has its usual derivative.
Article: main_krylov, the lower-majorant maximization in apC:sec:design. -/
theorem sech_hasDerivAt (x : ℝ) : HasDerivAt sech (-sech x * tanh x) x := by
  convert! (Real.hasDerivAt_cosh x).inv (Real.cosh_pos x).ne' using 1
  rw [sech, Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- The actual profile derivative has the source factorization.
Article: main_krylov, the displayed derivative in the proof of the Chebyshev majorants. -/
theorem sechProfile_hasDerivAt (x : ℝ) :
    HasDerivAt sechProfile (sech x * (1 - x * tanh x)) x := by
  convert! (hasDerivAt_id x).mul (sech_hasDerivAt x) using 1
  simp only [id_eq]
  ring

/-- The genuine lower-majorant profile is continuous everywhere.
Article: main_krylov, the discretized lower-majorant limit. -/
theorem sechProfile_continuous : Continuous sechProfile :=
  continuous_iff_continuousAt.mpr (fun x => (sechProfile_hasDerivAt x).continuousAt)

/-- Hyperbolic tangent is strictly increasing, from its actual positive derivative.
Article: main_krylov, uniqueness of the lower-majorant stationary point. -/
theorem tanh_strictMono : StrictMono tanh :=
  strictMono_of_hasDerivAt_pos tanh_derivative (fun x => sq_pos_of_pos (sech_pos x))

/-- The stationary-point expression y*tanh(y) strictly increases for y>=0.
Article: main_krylov, the equation characterizing the unique lower-majorant maximum. -/
theorem mul_tanh_strictMonoOn : StrictMonoOn (fun y : ℝ => y * tanh y) (Ici 0) := by
  intro x hx y _ hxy
  have htx : 0 ≤ tanh x := by simpa only [Real.tanh_zero] using tanh_strictMono.monotone hx
  calc
    x * tanh x ≤ y * tanh x := mul_le_mul_of_nonneg_right hxy.le htx
    _ < y * tanh y := mul_lt_mul_of_pos_left (tanh_strictMono hxy) (hx.trans_lt hxy)

/-- The stationary equation has an actual solution strictly between one and two.
Article: main_krylov, max_y y*sech(y), characterized by y*tanh(y)=1.
Proof: sinh(2)>=2 and cosh(2)^2-sinh(2)^2=1 give 2*tanh(2)>1;
the intermediate value theorem supplies the root, and tanh<1 puts it above one. -/
theorem sech_stationary_exists : ∃ y : ℝ, y ∈ Ioo 1 2 ∧ y * tanh y = 1 := by
  have hs : (2 : ℝ) ≤ sinh 2 := Real.self_le_sinh_iff.mpr (by norm_num)
  have hc := Real.cosh_sq_sub_sinh_sq 2
  have hp := Real.cosh_pos 2
  have h2s : cosh 2 < 2 * sinh 2 := by nlinarith
  have h2 : 1 < 2 * tanh 2 := by
    rw [Real.tanh_eq_sinh_div_cosh, ← mul_div_assoc]
    exact (lt_div_iff₀ hp).mpr (by simpa using h2s)
  have hct : Continuous tanh := continuous_iff_continuousAt.mpr
    (fun x => (tanh_derivative x).continuousAt)
  obtain ⟨y, hy, he⟩ := intermediate_value_Icc (a := (0 : ℝ)) (b := 2) (by norm_num)
    (continuous_id.mul hct).continuousOn
    (show (1 : ℝ) ∈ Icc (0 * tanh 0) (2 * tanh 2) from ⟨by norm_num, h2.le⟩)
  change y * tanh y = 1 at he
  have hy0 : 0 < y := by
    by_contra hn
    have hyz : y = 0 := le_antisymm (le_of_not_gt hn) hy.1
    rw [hyz] at he
    norm_num at he
  have h1 : 1 < y := by
    have h := mul_lt_mul_of_pos_left (Real.tanh_lt_one y) hy0
    rw [mul_one, he] at h
    exact h
  have hy2 : y < 2 := by
    apply lt_of_le_of_ne hy.2
    intro heq
    have hy2 : 2 * tanh 2 = 1 := by simpa only [heq] using he
    exact h2.ne' hy2
  exact ⟨y, ⟨h1, hy2⟩, he⟩

/-- The actual uniquely determined stationary point of the lower-majorant profile.
Article: main_krylov, max_y y*sech(y). -/
def sechOptimizer : ℝ := sech_stationary_exists.choose

/-- The constructed stationary point satisfies the actual source equation and bounds.
Article: main_krylov, the lower-majorant maximum. -/
theorem sechOptimizer_spec : sechOptimizer ∈ Ioo 1 2 ∧ sechOptimizer * tanh sechOptimizer = 1 :=
  sech_stationary_exists.choose_spec

/-- The stationary equation has exactly the constructed solution on the nonnegative half-line.
Article: main_krylov, uniqueness in the lower-majorant maximization. -/
theorem mul_tanh_eq_one_iff {y : ℝ} (hy : 0 ≤ y) :
    y * tanh y = 1 ↔ y = sechOptimizer := by
  constructor
  · intro he
    apply mul_tanh_strictMonoOn.injOn hy (show 0 ≤ sechOptimizer from le_trans (by norm_num) sechOptimizer_spec.1.1.le)
    exact he.trans sechOptimizer_spec.2.symm
  · rintro rfl
    exact sechOptimizer_spec.2

/-- The profile strictly increases up to its constructed stationary point.
Article: main_krylov, the lower-majorant maximum. -/
theorem sechProfile_strictMonoOn : StrictMonoOn sechProfile (Icc 0 sechOptimizer) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) sechProfile_continuous.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [(sechProfile_hasDerivAt x).deriv]
  apply mul_pos (sech_pos x)
  apply sub_pos.mpr
  rw [← sechOptimizer_spec.2]
  exact mul_tanh_strictMonoOn hx.1.le (show 0 ≤ sechOptimizer from le_trans (by norm_num) sechOptimizer_spec.1.1.le) hx.2

/-- The profile strictly decreases after its constructed stationary point.
Article: main_krylov, the lower-majorant maximum. -/
theorem sechProfile_strictAntiOn : StrictAntiOn sechProfile (Ici sechOptimizer) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _) sechProfile_continuous.continuousOn
  intro x hx
  rw [interior_Ici] at hx
  rw [(sechProfile_hasDerivAt x).deriv]
  apply mul_neg_of_pos_of_neg (sech_pos x)
  apply sub_neg.mpr
  rw [← sechOptimizer_spec.2]
  exact mul_tanh_strictMonoOn (show 0 ≤ sechOptimizer from le_trans (by norm_num) sechOptimizer_spec.1.1.le)
    (show 0 ≤ x from (le_trans (by norm_num) sechOptimizer_spec.1.1.le).trans hx.le) hx

/-- The source maximum is genuinely attained at the unique constructed stationary point.
Article: main_krylov, max_{y>=0} y*sech(y), rather than an assumed maximum. -/
theorem sechProfile_le_max {y : ℝ} (hy : 0 ≤ y) : sechProfile y ≤ sechProfile sechOptimizer := by
  by_cases h : y ≤ sechOptimizer
  · exact sechProfile_strictMonoOn.monotoneOn ⟨hy, h⟩
      ⟨show 0 ≤ sechOptimizer from le_trans (by norm_num) sechOptimizer_spec.1.1.le, le_rfl⟩ h
  · exact sechProfile_strictAntiOn.antitoneOn (Set.mem_Ici.mpr (le_refl sechOptimizer)) (le_of_not_ge h)
      (le_of_not_ge h)

/-- No other nonnegative point attains the maximum.
Article: main_krylov, the exact qualitative lower-majorant optimizer. -/
theorem sechProfile_eq_max_iff {y : ℝ} (hy : 0 ≤ y) :
    sechProfile y = sechProfile sechOptimizer ↔ y = sechOptimizer := by
  constructor
  · intro he
    rcases lt_trichotomy y sechOptimizer with h | h | h
    · exact False.elim ((sechProfile_strictMonoOn ⟨hy, h.le⟩
        ⟨show 0 ≤ sechOptimizer from le_trans (by norm_num) sechOptimizer_spec.1.1.le, le_rfl⟩ h).ne he)
    · exact h
    · exact False.elim ((sechProfile_strictAntiOn (Set.mem_Ici.mpr (le_refl sechOptimizer)) h.le h).ne he)
  · rintro rfl
    rfl

end
end krylov.Design
