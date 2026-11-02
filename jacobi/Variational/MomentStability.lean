import jacobi.Variational.Tightness

/-!
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Scheffe's lemma converts almost-everywhere convergence and exact mass
convergence of nonnegative densities into global L1 convergence. An explicit
spectral l1 estimate then controls every fixed positive integer moment of
the actual kernel spectrum. These facts retain all cyclic comparisons in
the general equimeasurable rearrangement limit.
Source: Scheffe's lemma and the elementary difference-of-powers estimate.
Use: once distribution identifies the exact limiting mass, every rearranged moment passes through global L1 convergence.
-/
namespace jacobi.Variational
noncomputable section
open Set Real MeasureTheory Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Scheffe's lemma for the actual nonnegative finite-mass density domain.
Use: once distribution identifies the exact limiting mass, every rearranged moment passes through global L1 convergence.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Source: Scheffe's lemma for nonnegative integrable functions.
Proof: min(m_n,q) is dominated by q and tends to q almost everywhere. Integrate
the identity |m_n-q|=m_n+q-2min(m_n,q) and use mass convergence. -/
theorem l1_limit_of_ae_mass_limit (m : ℕ → Density) (q : L1Source)
    (hae : ∀ᵐ x, Tendsto (fun n => (m n).value x) atTop (𝓝 (q.value x)))
    (hm : Tendsto (fun n => (m n).mass) atTop (𝓝 q.mass)) :
    Tendsto (fun n => ∫ x, |(m n).value x-q.value x|) atTop (𝓝 0) := by
  -- The integrable dominating function is the fixed limit, so a separate tightness estimate is unnecessary.
  have hi (n : ℕ) : Integrable (fun x => min ((m n).value x) (q.value x)) := by
    apply q.integrable.mono' ((m n).measurable.min q.measurable).aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_min ((m n).nonneg x) (q.nonneg x))]
      exact min_le_right _ _
  have ht := tendsto_integral_of_dominated_convergence (F := fun n x => min ((m n).value x) (q.value x))
    (f := q.value) q.value
    (fun n => ((m n).measurable.min q.measurable).aestronglyMeasurable) q.integrable
    (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_min ((m n).nonneg x) (q.nonneg x))]
      exact min_le_right _ _)
    (hae.mono fun x hx => by
      simpa only [min_self] using hx.min (tendsto_const_nhds (x := q.value x)))
  change Tendsto (fun n => ∫ x, min ((m n).value x) (q.value x)) atTop (𝓝 q.mass) at ht
  have he (n : ℕ) : (∫ x, |(m n).value x-q.value x|)=
      (m n).mass+q.mass-2*(∫ x, min ((m n).value x) (q.value x)) := by
    calc
      _ = ∫ x, (m n).value x+q.value x-2*min ((m n).value x) (q.value x) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by grind [abs_eq_max_neg]
      _ = _ := by
        have hs := integral_sub ((m n).integrable.add q.integrable) ((hi n).const_mul 2)
        have ha := integral_add (m n).integrable q.integrable
        simp only [Pi.add_apply] at hs ha
        rw [hs,ha,integral_const_mul]
        rfl
  have h := (hm.add_const q.mass).sub (ht.const_mul 2)
  simpa only [← he,show q.mass+q.mass-2*q.mass=0 by ring] using h

/-- Uniformly bounded nonnegative spectra have an explicit l1 modulus for every positive integer moment.
Use: controls all actual cyclic moments under L1 approximation of densities.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: bound each difference of powers by (n+1)M^n times the entry difference,
then sum the convergent nonnegative absolute-error series. -/
theorem power_distance {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b)
    (hna : ∀ j, 0 ≤ a j) (hnb : ∀ j, 0 ≤ b j) {M : ℝ}
    (hMa : ∀ j, a j ≤ M) (hMb : ∀ j, b j ≤ M) (n : ℕ) :
    |(∑' j, a j^(n+1))-(∑' j, b j^(n+1))| ≤ ((n : ℝ)+1)*M^n*distance a b := by
  -- The bound is at a fixed order and uses the common actual spectral mass bound.
  have haP := jacobi.Continuum.summable_powers ha hna (by omega : 0 < n+1)
  have hbP := jacobi.Continuum.summable_powers hb hnb (by omega : 0 < n+1)
  calc
    _ ≤ ∑' j, |a j^(n+1)-b j^(n+1)| := mass_distance haP hbP
    _ ≤ ∑' j, (((n : ℝ)+1)*M^n)*|a j-b j| := by
      apply (haP.sub hbP).abs.tsum_le_tsum _ ((ha.sub hb).abs.mul_left _)
      intro j
      have h := abs_pow_sub_pow_le (a := a j) (b := b j) (n := n+1)
      have hm : max |a j| |b j| ≤ M := by
        rw [abs_of_nonneg (hna j),abs_of_nonneg (hnb j)]
        exact max_le (hMa j) (hMb j)
      have hp := pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg (a j))) hm n
      simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at h
      nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ |a j-b j| *((n : ℝ)+1))]
    _ = _ := tsum_mul_left

/-- Every positive integer actual spectral moment converges under L1 density convergence with a common mass bound.
Use: all G_p inequalities survive the general equimeasurable rearrangement limit.
Article: jacobi, Appendix D.1 (full-density rearrangement and radial ground state).
Proof: trace equals mass bounds every eigenvalue; combine the power-distance
estimate with actual L1 spectral stability and squeeze the error to zero. -/
theorem moment_limit_of_l1 (m : ℕ → Density) (q : L1Source) {M : ℝ}
    (hM : ∀ n, (m n).mass ≤ M) (hq : q.mass ≤ M)
    (hl : Tendsto (fun n => ∫ x, |(m n).value x-q.value x|) atTop (𝓝 0)) (p : ℕ) :
    Tendsto (fun n => ∑' j, (m n).spectrum j^(p+1)) atTop
      (𝓝 (∑' j, q.spectrum j^(p+1))) := by
  -- The same trace bound controls every actual eigenvalue of every approximant and of the limit.
  have hb (r : L1Source) (hr : r.mass ≤ M) (j : ℕ) : r.spectrum j ≤ M := by
    let D := chebyshev2.Continuum.kernelSpectralData r.integrable r.nonneg
    have h := D.eigenvalue_summable.le_tsum j (fun k _ => D.eigenvalue_nonneg k)
    change r.spectrum j ≤ ∑' k, r.spectrum k at h
    rw [L1Source.spectrum,chebyshev2.Continuum.kernelEigenvalue_mass] at h
    exact h.trans hr
  have hM0 : 0 ≤ M := (integral_nonneg q.nonneg).trans hq
  have ht := hl.const_mul (((p : ℝ)+1)*M^p)
  rw [mul_zero] at ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ ht
  intro n
  rw [Real.norm_eq_abs]
  let D := chebyshev2.Continuum.kernelSpectralData (m n).integrable (m n).nonneg
  let Q := chebyshev2.Continuum.kernelSpectralData q.integrable q.nonneg
  exact (power_distance D.eigenvalue_summable Q.eigenvalue_summable
    D.eigenvalue_nonneg Q.eigenvalue_nonneg (hb (m n) (hM n)) (hb q hq) p).trans
      (mul_le_mul_of_nonneg_left (kernel_distance (m n).integrable q.integrable (m n).nonneg q.nonneg)
        (by positivity))

end
end jacobi.Variational
