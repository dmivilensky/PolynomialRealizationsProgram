import jacobi.Analytic.NormingMajorant
import jacobi.Reference.NormingBounds
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
The literal original norming products converge absolutely and uniformly,
are holomorphic, and have the required uniform inverse-square error.
Their real restrictions are exactly the earlier real norming ratios.
Source: mathlib's normally convergent product and Weierstrass theorems;
the estimates use the proved original complex Bessel spectrum.
Use: supplies the uniform convergence asserted by analytic GL, including the original finite spectral prefix.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric Filter jacobi.Hankel jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual continued norming product converges uniformly even on the closed order disk.
Use: supplies the uniform convergence asserted by analytic GL, including the original finite spectral prefix.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the actual factors are continuous on the compact closed disk and their deviations from one are bounded by the same proved summable majorant at every order. Apply the community uniform infinite-product theorem. -/
theorem OrderDisk.normingRatio_uniform {a0 : ℝ} (D : OrderDisk a0) (k : ℕ) :
    HasProdUniformlyOn (D.normingFactor k) (D.normingRatio k) (closedBall (a0:ℂ) D.radius) := by
  -- All factors and both limits here are the literal source products.
  change HasProdUniformlyOn (fun l a => D.normingFactor k l a)
    (fun a => ∏' l,D.normingFactor k l a) _
  have hh := (D.normingMajorant_summable k).hasProdUniformlyOn_one_add
    (f := fun l a => D.normingFactor k l a-1) (isCompact_closedBall _ _)
    (Eventually.of_forall (fun l a ha => D.normingFactor_bound
      (by simpa only [mem_closedBall,dist_eq_norm] using ha) k l))
    (fun l => (D.normingFactor_continuousOn k l).sub continuousOn_const)
  convert! hh using 1 <;> simp only [add_sub_cancel]

/-- Every genuine continued norming ratio is holomorphic on the common original order disk.
Use: the spectral weights in the analytic GL kernel depend holomorphically on the order.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: finite products of the actual nonvanishing-denominator holomorphic factors are holomorphic. Their proved closed-disk uniform convergence implies local uniform convergence on the open disk, so the community Weierstrass theorem applies. -/
theorem OrderDisk.normingRatio_holomorphic {a0 : ℝ} (D : OrderDisk a0) (k : ℕ) :
    DifferentiableOn ℂ (D.normingRatio k) (ball (a0:ℂ) D.radius) := by
  have hh := ((D.normingRatio_uniform k).mono ball_subset_closedBall).tendstoUniformlyOn
  exact hh.tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall (fun _ => DifferentiableOn.fun_finsetProd
      (fun l _ => D.normingFactor_holomorphic k l))) isOpen_ball

/-- None of the actual continued gap factors vanishes anywhere on the closed disk.
Use: the normally convergent norming products are nonzero, as required for genuine spectral weights.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the diagonal factor is one. Off the diagonal the genuine reference separation makes the numerator nonzero and the actual Bessel separation makes the denominator nonzero. -/
theorem OrderDisk.normingFactor_ne_zero {a0 : ℝ} (D : OrderDisk a0) {a : ℂ}
    (ha : ‖a-(a0:ℂ)‖≤D.radius) (k l : ℕ) : D.normingFactor k l a≠0 := by
  -- Both spectral sequences are the source sequences continued on the same disk.
  unfold OrderDisk.normingFactor
  split_ifs with hlk
  · exact one_ne_zero
  · have hkl : k≠l := Ne.symm hlk
    exact div_ne_zero (norm_pos_iff.mp ((mul_pos (by norm_num) (quadratic_gap_pos hkl)).trans_le
      (frequencyReference_separated (D.admissible ha) hkl))) (D.gap_ne_zero ha hkl)

/-- The actual infinite norming ratio is nonzero throughout the closed estimation disk.
Use: the analytic continuation retains genuine nondegenerate norming weights.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the original factors are all nonzero and their deviations from one have a proved absolutely convergent norm series. The community nonvanishing product theorem applies to these actual factors. -/
theorem OrderDisk.normingRatio_ne_zero {a0 : ℝ} (D : OrderDisk a0) {a : ℂ}
    (ha : ‖a-(a0:ℂ)‖≤D.radius) (k : ℕ) : D.normingRatio k a≠0 := by
  simpa only [add_sub_cancel,OrderDisk.normingRatio] using
    tprod_one_add_ne_zero_of_summable
      (f := fun l => D.normingFactor k l a-1)
      (by simpa only [add_sub_cancel] using D.normingFactor_ne_zero ha k)
      (D.normingFactor_summable ha k)

/-- The genuine continued norming ratios have one uniform bound and one uniform inverse-square error bound on the whole closed disk.
Use: supplies the quantitative norming estimates in the actual analytic GL series.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: each finite product differs from one by at most exp of the sum of its factor errors minus one. The actual common majorant bounds every such sum by E/(k+1)^2. Pass this estimate to the genuine product limit; the exponential remainder inequality then gives E*exp(E)/(k+1)^2. The triangle inequality bounds the product itself. -/
theorem OrderDisk.normingRatio_bounds {a0 : ℝ} (D : OrderDisk a0) :
    ∃ C : ℝ,0<C ∧ ∀ a : ℂ,‖a-(a0:ℂ)‖≤D.radius → ∀ k : ℕ,
      ‖D.normingRatio k a‖≤C ∧ ‖D.normingRatio k a-1‖≤C/(k+1:ℝ)^2 := by
  -- The finite-product estimate avoids any unproved complex logarithm branch selection.
  obtain ⟨E,hE,hrows⟩ := D.normingMajorant_sum_bound
  refine ⟨1+E*Real.exp E,by positivity,fun a ha k => ?_⟩
  have hs := D.normingFactor_summable ha k
  have hm : Multipliable (fun l => D.normingFactor k l a) := by
    simpa only [add_sub_cancel] using multipliable_one_add_of_summable hs
  have hsum : (∑' l,‖D.normingFactor k l a-1‖)≤E/(k+1:ℝ)^2 :=
    (hs.tsum_le_tsum (fun l => D.normingFactor_bound ha k l)
      (D.normingMajorant_summable k)).trans (hrows k)
  have hlimit : Tendsto (fun T : Finset ℕ => ∏ l∈T,D.normingFactor k l a) atTop
      (𝓝 (D.normingRatio k a)) := hm.hasProd
  have hprod : ‖D.normingRatio k a-1‖≤Real.exp (E/(k+1:ℝ)^2)-1 := by
    apply le_of_tendsto (hlimit.sub_const 1).norm
    apply Eventually.of_forall
    intro T
    have hh := T.norm_prod_one_add_sub_one_le (fun l => D.normingFactor k l a-1)
    simp only [add_sub_cancel] at hh
    exact hh.trans (sub_le_sub_right (Real.exp_le_exp.mpr
      ((hs.sum_le_tsum T (fun _ _ => norm_nonneg _)).trans hsum)) 1)
  have hsq : 1≤(k+1:ℝ)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hsmall : E/(k+1:ℝ)^2≤E := div_le_self hE.le hsq
  have herr : ‖D.normingRatio k a-1‖≤E*Real.exp E/(k+1:ℝ)^2 := by
    have he := exp_sub_one_bound (E/(k+1:ℝ)^2)
    rw [abs_of_nonneg (div_nonneg hE.le (sq_nonneg _))] at he
    calc
      _ ≤ Real.exp (E/(k+1:ℝ)^2)-1 := hprod
      _ ≤ (E/(k+1:ℝ)^2)*Real.exp (E/(k+1:ℝ)^2) := (le_abs_self _).trans he
      _ ≤ (E/(k+1:ℝ)^2)*Real.exp E := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hsmall) (by positivity)
      _ = _ := by ring
  refine ⟨?_,herr.trans (by gcongr; linarith)⟩
  have hh := norm_add_le (D.normingRatio k a-1) (1:ℂ)
  rw [sub_add_cancel,norm_one] at hh
  have hh' := herr.trans (div_le_self (by positivity) hsq)
  linarith

/-- Every continued original gap factor agrees with the earlier real factor on the real part of the disk.
Use: identifies the product weights of analytic GL with the original real construction.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: the actual continued Bessel branches retain their numbered real zeros and the continued polynomial reference values restrict to the original real eigenvalues; real inclusion preserves the quotient. -/
theorem OrderDisk.normingFactor_real {a0 : ℝ} (D : OrderDisk a0) {b : ℝ}
    (hb : -1<b) (hbd : ‖(b:ℂ)-(a0:ℂ)‖≤D.radius) (k l : ℕ) :
    D.normingFactor k l (b:ℂ)=(jacobi.Reference.normingFactor b hb k l:ℂ) := by
  unfold OrderDisk.normingFactor jacobi.Reference.normingFactor
  split_ifs
  · rfl
  · rw [D.real_eq b hb hbd l,D.real_eq b hb hbd k,
      frequencyReference_ofReal,frequencyReference_ofReal]
    push_cast
    rfl

/-- The actual continued infinite product equals the original real norming ratio at every real order of the disk.
Use: the analytic GL kernel uses exactly the previously proved real spectral weights.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: map the genuinely convergent original real product through the continuous real inclusion. Its factors are the proved continued factors, so uniqueness of the actual product limit identifies the two ratios. -/
theorem OrderDisk.normingRatio_real {a0 : ℝ} (D : OrderDisk a0) {b : ℝ}
    (hb : -1<b) (hbd : ‖(b:ℂ)-(a0:ℂ)‖≤D.radius) (k : ℕ) :
    D.normingRatio k (b:ℂ)=(jacobi.Reference.normingRatio b hb k:ℂ) := by
  have hh := (jacobi.Reference.normingRatio_properties hb k).1.map
    Complex.ofRealHom Complex.continuous_ofReal
  have he : (Complex.ofRealHom ∘ jacobi.Reference.normingFactor b hb k)=
      (fun l => D.normingFactor k l (b:ℂ)) := by
    funext l
    exact (D.normingFactor_real hb hbd k l).symm
  rw [he] at hh
  exact hh.tprod_eq

/-- The original complex norming products satisfy the complete quantitative and holomorphic assertion of analytic GL at every admissible real base order, and agree with the real construction.
Use: supplies Appendix E.1 without any unproved spectral, convergence,
or continuation premise; the following GL kernel construction uses this same disk.
Article: jacobi, Appendix E.1 (holomorphic norming, GL reconstruction and energy).
Proof: obtain the actual numbered Bessel order disk from the proved full
zero theorem, and combine the literal product's absolute convergence,
closed-disk uniform convergence, holomorphy, quantitative bounds and exact
real restriction. Every constant is supplied by those proved estimates. -/
theorem analytic_norming_products {a0 : ℝ} (ha0 : -1<a0) :
    ∃ D : OrderDisk a0,∃ C : ℝ,0<C ∧ ∀ k : ℕ,
      HasProdUniformlyOn (D.normingFactor k) (D.normingRatio k) (closedBall (a0:ℂ) D.radius) ∧
      DifferentiableOn ℂ (D.normingRatio k) (ball (a0:ℂ) D.radius) ∧
      (∀ a : ℂ,‖a-(a0:ℂ)‖≤D.radius →
        Summable (fun l => ‖D.normingFactor k l a-1‖) ∧ D.normingRatio k a≠0 ∧
          ‖D.normingRatio k a‖≤C ∧ ‖D.normingRatio k a-1‖≤C/(k+1:ℝ)^2) ∧
      (∀ b : ℝ,∀ hb : -1<b,‖(b:ℂ)-(a0:ℂ)‖≤D.radius →
        D.normingRatio k (b:ℂ)=(jacobi.Reference.normingRatio b hb k:ℂ)) := by
  -- The only input is the original admissible real base order, not a spectral certificate.
  obtain ⟨D⟩ := orderDisk_nonempty ha0
  obtain ⟨C,hC,hbound⟩ := D.normingRatio_bounds
  exact ⟨D,C,hC,fun k => ⟨D.normingRatio_uniform k,D.normingRatio_holomorphic k,
    (fun a ha => ⟨D.normingFactor_summable ha k,D.normingRatio_ne_zero ha k,hbound a ha k⟩),
    (fun b hb hbd => D.normingRatio_real hb hbd k)⟩⟩

end
end jacobi.Analytic
