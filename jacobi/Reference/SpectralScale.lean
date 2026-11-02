import jacobi.Reference.Parameters
import jacobi.Bessel.SpectralBounds

/-!
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Both genuine original spectra have a common increasing linear frequency
scale, with a unit complex energy margin for all sufficiently large original
indices. Every premise comes from the actual Bessel roots and the literal
reference spectrum, including all fixed potential shifts.
Use: applies the genuine energy-disk reference estimates simultaneously at every original Bessel and reference spectral value and between them.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Both true original spectra lie above one common squared index scale with a unit complex energy margin for all sufficiently large actual indices.
Use: applies the genuine energy-disk reference estimates simultaneously at every original Bessel and reference spectral value and between them.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: use the proved genuine linear Bessel-root lower bound and the
literal positive reference phase lower bound. Choose a smaller common
linear scale, then absorb the original fixed potential shift and the
unit disk margin at large indices. -/
theorem spectral_energy_scale {a : ℝ} (ha : -1<a) :
    ∃ d : ℝ,0<d ∧ ∀ᶠ k:ℕ in atTop,1≤d*(k+1:ℝ) ∧
      (d*(k+1:ℝ))^2+1≤eigenvalue a k- jacobi.Jacobi.endpointCorrection a ∧
      (d*(k+1:ℝ))^2+1≤ jacobi.Bessel.sigma a ha k- jacobi.Jacobi.endpointCorrection a := by
  -- All lower bounds concern the genuine original enumeration; no replacement spectral sequence is introduced.
  obtain ⟨l,L,hl,_,hroots⟩ := jacobi.Bessel.positiveZero_linear_bounds ha
  let d := min (l/2) (Real.pi/8)
  have hd : 0<d := lt_min (by positivity) (by positivity)
  obtain ⟨K,hK⟩ := exists_nat_gt ((|jacobi.Jacobi.endpointCorrection a|+2)/d)
  refine ⟨d,hd,?_⟩
  filter_upwards [eventually_ge_atTop K] with k hk
  have hcast : (K:ℝ)≤k := by exact_mod_cast hk
  have hbig : |jacobi.Jacobi.endpointCorrection a|+2<d*(k+1:ℝ) := by
    have hh := (div_lt_iff₀ hd).mp hK
    nlinarith [mul_le_mul_of_nonneg_left hcast hd.le]
  have hr : 0<d*(k+1:ℝ) := by positivity
  have hlarge : 2<d*(k+1:ℝ) := by linarith [abs_nonneg (jacobi.Jacobi.endpointCorrection a)]
  have hreference : 2*d*(k+1:ℝ)≤Real.pi*((k:ℝ)+gamma a) := by
    have hdpi : d≤Real.pi/8 := min_le_right _ _
    have hm := mul_le_mul_of_nonneg_right hdpi (show 0≤2*(k+1:ℝ) by positivity)
    have hg := (parameters ha).1
    nlinarith [Nat.cast_nonneg (α := ℝ) k,Real.pi_pos]
  have hbessel : 2*d*(k+1:ℝ)≤ jacobi.Bessel.positiveZero a ha k := by
    have hdl : d≤l/2 := min_le_left _ _
    have hm := mul_le_mul_of_nonneg_right hdl (show 0≤2*(k+1:ℝ) by positivity)
    linarith [(hroots k).1]
  have hrefr : 0≤Real.pi*((k:ℝ)+gamma a) := by
    have hg := (parameters ha).1
    positivity
  have hbesr := (jacobi.Bessel.positiveZero_properties ha k).1
  have hrefsq := (sq_le_sq₀ (show 0≤2*d*(k+1:ℝ) by positivity) hrefr).mpr hreference
  have hbessq := (sq_le_sq₀ (show 0≤2*d*(k+1:ℝ) by positivity) hbesr.le).mpr hbessel
  refine ⟨by linarith [abs_nonneg (jacobi.Jacobi.endpointCorrection a)],?_,?_⟩
  · unfold eigenvalue
    nlinarith [sq_nonneg (d*(k+1:ℝ)-1)]
  · rw [← (jacobi.Bessel.positiveZero_properties ha k).2]
    nlinarith [sq_nonneg (d*(k+1:ℝ)-1),le_abs_self (jacobi.Jacobi.endpointCorrection a),
      abs_nonneg (jacobi.Jacobi.endpointCorrection a)]

end
end jacobi.Reference
