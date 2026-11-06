import nesterov.Flow.SpreadBounds

/-! Article: Lemma `lem:spread`, the exact equally weighted midpoint spectrum. -/
namespace nesterov.Flow
noncomputable section
open Finset Set

theorem midpoint_mem {J j : ℕ} (hJ : 0<J) (hj : j<J) : midpoint J j∈Icc (1:ℝ) 2 := by
  have hJp : (0:ℝ)<J := Nat.cast_pos.mpr hJ
  have hj' : (j:ℝ)+1≤J := by exact_mod_cast hj
  dsimp [midpoint]
  constructor
  · exact le_add_of_nonneg_right (by positivity)
  · have hh : ((j:ℝ)+1/2)/(J:ℝ)≤1 := (div_le_one hJp).mpr (by linarith)
    linarith

def midpointSpectrum (J : ℕ) (hJ : 0<J) (γ₀ : ℝ) (hγ₀ : 0≤γ₀) : Spectrum (Fin J) where
  frequency j := γ₀*midpoint J j
  weight _ := 1/(J:ℝ)
  frequency_nonneg j := mul_nonneg hγ₀ (le_trans (by norm_num) (midpoint_mem hJ j.isLt).1)
  weight_nonneg _ := by positivity
  weight_sum := by simp [ne_of_gt (Nat.cast_pos.mpr hJ : (0:ℝ)<J)]

theorem midpointSpectrum_frequency_bounds {J : ℕ} (hJ : 0<J) {γ₀ : ℝ} (hg : 0≤γ₀)
    (j : Fin J) : γ₀≤(midpointSpectrum J hJ γ₀ hg).frequency j ∧
      (midpointSpectrum J hJ γ₀ hg).frequency j≤2*γ₀ := by
  have hh := midpoint_mem hJ j.isLt
  dsimp [midpointSpectrum]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hh.1 hg,mul_le_mul_of_nonneg_left hh.2 hg]

theorem midpointSpectrum_average {J : ℕ} (hJ : 0<J) {γ₀ : ℝ} (hg : 0≤γ₀) (f : ℝ→ℝ) :
    (midpointSpectrum J hJ γ₀ hg).average f=
      midpointAverage J (fun lam=>f (γ₀*lam)) := by
  unfold Spectrum.average midpointSpectrum midpointAverage
  rw [mul_sum,←Fin.sum_univ_eq_sum_range]

theorem midpointSpectrum_secondMoment {J : ℕ} (hJ : 0<J) {γ₀ : ℝ} (hg : 0≤γ₀) :
    (midpointSpectrum J hJ γ₀ hg).average (fun γ=>γ^2)=
      γ₀^2*midpointAverage J (fun lam=>lam^2) := by
  rw [midpointSpectrum_average]
  simp only [midpointAverage,mul_pow,←mul_sum]
  ring

theorem midpointSpectrum_cosMoment {J : ℕ} (hJ : 0<J) {γ₀ : ℝ} (hg : 0≤γ₀) (q : ℝ) :
    (midpointSpectrum J hJ γ₀ hg).average (fun γ=>γ^2*Real.cos (γ*q))=
      γ₀^2*midpointAverage J (fun lam=>lam^2*Real.cos (lam*(γ₀*q))) := by
  rw [midpointSpectrum_average]
  simp only [midpointAverage,mul_sum]
  apply sum_congr rfl
  intro j _
  rw [show γ₀*midpoint J j*q=midpoint J j*(γ₀*q) by ring]
  ring

theorem midpoint_secondMoment_bounds {J : ℕ} (hJ : 0<J) :
    1≤midpointAverage J (fun lam=>lam^2) ∧ midpointAverage J (fun lam=>lam^2)≤4 := by
  have hh := midpointSpectrum_frequency_bounds hJ (show (0:ℝ)≤1 by norm_num)
  have h₁ := (midpointSpectrum J hJ 1 (by norm_num)).le_average
    (f:=fun γ=>γ^2) (C:=1) (fun j=>by have hj:=hh j; nlinarith [hj.1])
  have h₂ := (midpointSpectrum J hJ 1 (by norm_num)).average_le
    (f:=fun γ=>γ^2) (C:=4) (fun j=>by have hj:=hh j; nlinarith [hj.1,hj.2])
  simpa [midpointSpectrum_secondMoment] using And.intro h₁ h₂

theorem midpoint_cosMoment_abs_le {J : ℕ} (hJ : 0<J) (x : ℝ) :
    |midpointAverage J (fun lam=>lam^2*Real.cos (lam*x))|≤midpointAverage J (fun lam=>lam^2) := by
  have hJp : (0:ℝ)<J := Nat.cast_pos.mpr hJ
  unfold midpointAverage
  rw [abs_mul,abs_of_pos (div_pos zero_lt_one hJp)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro j _
  rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
  exact mul_le_of_le_one_right (sq_nonneg _) (Real.abs_cos_le_one _)


theorem midpointSpectrum_Umoment {J : ℕ} (hJ : 0<J) {γ₀ : ℝ} (hg : 0≤γ₀) (q : ℝ) :
    (midpointSpectrum J hJ γ₀ hg).average (fun γ=>γ^2*(1-Real.cos (γ*q)))=
      γ₀^2*midpointAverage J (fun lam=>lam^2*(1-Real.cos (lam*(γ₀*q)))) := by
  rw [midpointSpectrum_average]
  simp only [midpointAverage,mul_sum]
  apply sum_congr rfl
  intro j _
  rw [show γ₀*midpoint J j*q=midpoint J j*(γ₀*q) by ring]
  ring

end
end nesterov.Flow
