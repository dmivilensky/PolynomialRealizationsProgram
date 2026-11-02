import jacobi.Variational.FredholmSeries
import jacobi.Variational.FredholmRelaxation

/-!
Article: jacobi, Theorem D.7.
Every stated edge spectrum gives a positive finite Fredholm target strictly
below the concentrated scalar threshold at its actual total mass. Thus the
proved direct method and canonical optimizer apply without an additional
feasibility, finite-target or pole-margin hypothesis on the edge data.
Source: the complete nonnegative Fredholm moment series and strict edge moment bounds.
Use: the closed-form calibration solves precisely the original spectral threshold equation.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The real Fredholm target of an arbitrary actual edge spectrum below its stated top pole.
Use: the closed-form calibration solves precisely the original spectral threshold equation.
Article: jacobi, Theorem D.7.
-/
def target (Λ : EdgeSpectrum) (s : ℝ) : ℝ := ∑' j,fredholmLog s (Λ.value j)

/-- The printed real target is the genuine finite extended spectral Fredholm value.
Use: removes any unproved finiteness assumption from the edge-spectrum optimizer construction.
Article: jacobi, Theorem D.7.
Proof: the actual ordered summable spectrum has the uniform positive pole
margin 1-s*Lambda_1, so the verified spectral summability theorem applies. -/
theorem edge_target_eq (Λ : EdgeSpectrum) {s : ℝ} (hs : 0≤s) (hp : s*Λ.value 0<1) :
    Λ.fredholm s=ENNReal.ofReal (target Λ s) := by
  apply fredholmSpectrum_eq hs (sub_pos.mpr hp) Λ.summable (fun j => (Λ.positive j).le)
  intro j
  nlinarith [mul_le_mul_of_nonneg_left (Λ.antitone (Nat.zero_le j)) hs]

/-- Every actual edge moment is bounded by the corresponding power of its actual total mass.
Use: compares the complete Fredholm series with its concentrated scalar threshold.
Article: jacobi, Theorem D.7.
Proof: the common positive-moment estimate bounds the sum by Lambda_1^(p-1)*M, and Lambda_1<=M. -/
theorem edge_power_bound (Λ : EdgeSpectrum) (n : ℕ) : (∑' j,Λ.value j^(n+2))≤Λ.mass^(n+2) := by
  have hh := jacobi.Continuum.moment_bound Λ.summable (fun j => (Λ.positive j).le) Λ.antitone (n+1)
  change (∑' j,Λ.value j^(n+2))≤Λ.value 0^(n+1)*Λ.mass at hh
  exact hh.trans ((mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Λ.positive 0).le Λ.top_lt_mass.le (n+1)) Λ.mass_pos.le).trans_eq (by ring))

/-- The actual finite edge target is strictly below the full scalar Fredholm threshold at the actual mass.
Use: proves the exact strict-feasibility premise of the existing Fredholm direct method for every edge spectrum.
Article: jacobi, Theorem D.7.
Proof: compare the complete extended nonnegative moment series term by
term. Every moment is at most M^p; the second moment is strictly smaller.
The positive s²/2 coefficient gives a strict comparison without any assumption on s*M. -/
theorem edge_target_subcritical (Λ : EdgeSpectrum) {s : ℝ} (hs : 0<s) (hp : s*Λ.value 0<1) :
    ENNReal.ofReal (target Λ s)<fredholmTerm s Λ.mass := by
  -- The scalar threshold retains its infinite branch; no logarithm is evaluated there.
  rw [← edge_target_eq Λ hs.le hp,EdgeSpectrum.fredholm,fredholmSpectrum_series hs.le Λ.summable (fun j => (Λ.positive j).le),
    fredholmTerm_series hs.le Λ.mass_pos.le]
  have hfinite : (∑' n : ℕ,ENNReal.ofReal (s^(n+2)/((n:ℝ)+2))*ENNReal.ofReal (∑' j,Λ.value j^(n+2)))≠∞ := by
    rw [← fredholmSpectrum_series hs.le Λ.summable (fun j => (Λ.positive j).le),← EdgeSpectrum.fredholm,
      edge_target_eq Λ hs.le hp]
    exact ENNReal.ofReal_ne_top
  apply ENNReal.tsum_lt_tsum hfinite (i := 0)
  · intro n
    rw [show (s*Λ.mass)^(n+2)/((n:ℝ)+2)=(s^(n+2)/((n:ℝ)+2))*Λ.mass^(n+2) by rw [mul_pow]; ring,
      ENNReal.ofReal_mul (by positivity : 0≤s^(n+2)/((n:ℝ)+2))]
    exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (edge_power_bound Λ n)) (by positivity)
  · norm_num only [Nat.cast_zero,zero_add,Nat.reduceAdd]
    rw [← ENNReal.ofReal_mul (by positivity : 0≤s^2/(2:ℝ)),mul_pow]
    have hm := Λ.mass_pos
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    have hstrict := mul_lt_mul_of_pos_left Λ.second_lt_mass_sq (by positivity : 0<s^2/(2:ℝ))
    unfold EdgeSpectrum.second at hstrict
    nlinarith

/-- The actual real Fredholm target is strictly positive for every positive allowed coupling.
Use: the canonical optimizer is nonzero without an additional target-positivity premise.
Article: jacobi, Theorem D.7.
Proof: the first positive edge eigenvalue contributes a positive quadratic
term to the full nonnegative Fredholm series. Its extended positive value
equals ofReal of the genuine finite real target. -/
theorem edge_target_pos (Λ : EdgeSpectrum) {s : ℝ} (hs : 0<s) (hp : s*Λ.value 0<1) : 0<target Λ s := by
  -- Use one actual strictly positive spectral summand, never a truncated replacement for the target.
  have hquad : 0<fredholmTerm s (Λ.value 0) := by
    rw [fredholmTerm_series hs.le (Λ.positive 0).le]
    have hh := ENNReal.le_tsum (f := fun n : ℕ => ENNReal.ofReal ((s*Λ.value 0)^(n+2)/((n:ℝ)+2))) 0
    have hp0 : 0<(s*Λ.value 0)^2/(2:ℝ) := div_pos (sq_pos_of_pos (mul_pos hs (Λ.positive 0))) (by norm_num)
    norm_num only [Nat.cast_zero,zero_add] at hh
    exact (ENNReal.ofReal_pos.mpr hp0).trans_le hh
  have hh : 0<Λ.fredholm s := hquad.trans_le (ENNReal.le_tsum (f := fun j => fredholmTerm s (Λ.value j)) 0)
  rw [edge_target_eq Λ hs.le hp] at hh
  exact ENNReal.ofReal_pos.mp hh

end
end jacobi.Fredholm
