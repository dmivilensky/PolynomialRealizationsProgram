import jacobi.Analytic.FiniteShiftedSpectrum

/-!
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
The entire actual shifted finite Jacobi spectrum converges in L1,
uniformly on every compact subset of the original slit plane. The
proof uses the already proved unshifted L1 convergence and one exact
resolvent difference, with all finite denominators controlled internally.
Use: finiteShiftedEdge_l1_uniform sums the actual full spectral errors, without cutting the spectrum into a numerical prefix and tail.
-/
namespace jacobi.EdgeResolvent
noncomputable section
open Real Set Filter
open scoped Topology

/-- The exact genuine resolvent comparison has the common original
compact Lipschitz bound for every real spectral pair with bounded inverses.
Use: finiteShiftedEdge_l1_uniform sums the actual full spectral errors,
without cutting the spectrum into a numerical prefix and tail.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: use the exact original difference formula; complex norms are
multiplicative and both actual inverse denominators have the same bound. -/
theorem resolventTransform_sub_bound {r s C:ℝ} {w:ℂ}
    (hr:1+((r/2:ℝ):ℂ)*w≠0) (hs:1+((s/2:ℝ):ℂ)*w≠0)
    (hC:0≤C) (hR:‖(1+((r/2:ℝ):ℂ)*w)⁻¹‖≤C) (hS:‖(1+((s/2:ℝ):ℂ)*w)⁻¹‖≤C) :
    ‖resolventTransform r w-resolventTransform s w‖≤C^2*|r-s| := by
  rw [resolventTransform_sub r s w hr hs,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hR (abs_nonneg (r-s))) hS (norm_nonneg _) (mul_nonneg (abs_nonneg _) hC)
  exact hh.trans_eq (by ring)

/-- The complete actual shifted finite spectrum converges in its genuine
L1 norm uniformly over every original compact slit-domain shift set.
Use: all finite shifted-resolvent limits of Theorem C.5 retain a common
compact error, rather than a separate convergence premise at each shift.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: the actual finite and limiting inverse denominators have one
proved common compact bound. Their exact original resolvent difference
is bounded by that constant squared times each genuine unshifted
spectral error. The whole summable error is bounded by the actual L1
distance, which tends to zero without any additional rate assumption. -/
theorem finiteShiftedEdge_l1_uniform {a b:ℝ} (ha:-1<a) (hb:-1<b)
    {W:Set ℂ} (hW:IsCompact W) (hsub:W⊆edgeDomain a ha) :
    ∀ε:ℝ,0<ε→∃N:ℕ,∀n≥N,∀w∈W,
      (∑'k,‖finiteShiftedEdge a b ha hb n k w-shiftedEdge a ha k w‖)<ε := by
  -- Summability and the common comparison are established for the actual complete spectra.
  obtain ⟨C,hC,hbound⟩ := finite_denominator_compact ha hb hW hsub
  obtain ⟨NC,hNC⟩ := eventually_atTop.mp hbound
  have hd := (jacobi.Jacobi.finiteLambdaAt_l1_tendsto ha hb).comp (tendsto_add_atTop_nat 1)
  have hsmall := hd.const_mul (C^2)
  simp only [mul_zero] at hsmall
  intro ε hε
  obtain ⟨ND,hND⟩ := eventually_atTop.mp (hsmall.eventually (Iio_mem_nhds hε))
  refine ⟨max NC ND,fun n hn w hw => ?_⟩
  have hS := ((jacobi.Jacobi.finiteLambdaAt_summable ha hb (n+1)).sub (jacobi.Bessel.edgeValue_summable ha)).abs
  have hbnd (k:ℕ) : ‖finiteShiftedEdge a b ha hb n k w-shiftedEdge a ha k w‖≤
      C^2*|jacobi.Jacobi.finiteLambdaAt a b ha hb (n+1) k- jacobi.Bessel.edgeValue a ha k| := by
    have hh := hNC n (by omega) k w hw
    rw [finiteShiftedEdge,shiftedEdge_transform a ha k (hsub hw)]
    have hne := slit_denominator_ne
      (jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha 0)) (inverse_sigma_mem a ha k) (hsub hw)
    have hy : jacobi.Bessel.edgeValue a ha k/2=1/ jacobi.Bessel.sigma a ha k := by rw [jacobi.Bessel.edgeValue]; ring
    rw [← hy] at hne
    exact resolventTransform_sub_bound hh.1 hne hC.le hh.2.1 hh.2.2
  have hsNorm := (hS.mul_left (C^2)).of_nonneg_of_le (fun _ => norm_nonneg _) hbnd
  have hle := Summable.tsum_le_tsum hbnd hsNorm (hS.mul_left (C^2))
  rw [tsum_mul_left] at hle
  exact hle.trans_lt (hND n (by omega))

end
end jacobi.EdgeResolvent
