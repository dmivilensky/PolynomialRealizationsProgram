import jacobi.Bessel.ProductContinuity

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The actual normalized entire Bessel function equals the convergent product
over all of its genuine squared zeros, at every complex spectral parameter.
The proof passes the exact finite Jacobi products through the proved L1 limit.
Use: all finite and infinite spectral products below are genuine convergent products.
-/
namespace jacobi.Bessel
noncomputable section
open Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Absolute summability of the actual complex canonical-product perturbations.
Use: all finite and infinite spectral products below are genuine convergent products.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: the norm is the fixed complex scalar norm times the nonnegative summable real entry. -/
theorem complex_spectral_summable (z : ℂ) {f : ℕ → ℝ} (hf : Summable f)
    (hn : ∀ k,0≤f k) : Summable (fun k => ‖z*(f k:ℂ)‖) := by
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hn _)] using hf.mul_left ‖z‖

/-- The complex spectral product over the actual finite padded spectrum equals the literal original normalized Jacobi function.
Use: the product continuity limit and Mehler--Heine concern exactly the same finite functions.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: every padded factor is one. Reduce to the finite roots and apply
the proved exact normalized finite product, cancelling only the constant two. -/
theorem finite_canonical_product {a b : ℝ} (ha : -1<a) (hb : -1<b)
    {n : ℕ} (hn : 0<n) (z : ℂ) :
    (∏' k:ℕ,(1+(-z/2)*(jacobi.Jacobi.finiteLambdaAt a b ha hb n k:ℂ)))=
      jacobi.Jacobi.normalized (a:ℂ) (b:ℂ) n (1-z/(2*(n:ℂ)^2)) := by
  -- The infinite product is actually finite here, with proved unit factors beyond the degree.
  rw [tprod_eq_prod (s := Finset.range n) (by
    intro k hk
    rw [jacobi.Jacobi.finiteLambdaAt_zero ha hb (by simpa only [Finset.mem_range,not_lt] using hk)]
    simp)]
  rw [← Fin.prod_univ_eq_prod_range,jacobi.Jacobi.normalized_scaled_product ha hb hn]
  apply Finset.prod_congr rfl
  intro i _
  rw [jacobi.Jacobi.finiteLambdaAt_eq ha hb i.isLt,jacobi.Jacobi.finiteLambda]
  push_cast
  ring

/-- The true complex products of the finite Jacobi spectra converge to the genuine infinite Bessel spectral product.
Use: identifies the infinite product with the independently known Mehler--Heine limit, excluding any extra entire factor.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: the product perturbation estimate bounds the error by a fixed
exponential mass constant times the proved full spectral L1 distance.
The finite trace is uniformly bounded in positive degree. -/
theorem finite_canonical_product_tendsto {a b : ℝ} (ha : -1<a) (hb : -1<b) (z : ℂ) :
    Tendsto (fun n : ℕ => ∏' k:ℕ,(1+(-z/2)*(jacobi.Jacobi.finiteLambdaAt a b ha hb n k:ℂ)))
      atTop (𝓝 (∏' k:ℕ,(1+(-z/2)*(edgeValue a ha k:ℂ)))) := by
  -- Neither product equality nor a uniform summable bound on the finite spectra is assumed.
  let u (n k : ℕ) : ℂ := (-z/2)*(jacobi.Jacobi.finiteLambdaAt a b ha hb n k:ℂ)
  let v (k : ℕ) : ℂ := (-z/2)*(edgeValue a ha k:ℂ)
  let C : ℝ := Real.exp (‖-z/2‖*(jacobi.Jacobi.traceBound a b+1/(2*(a+1))))
  have hu n := complex_spectral_summable (-z/2) (jacobi.Jacobi.finiteLambdaAt_summable ha hb n)
    (jacobi.Jacobi.finiteLambdaAt_nonneg ha hb n)
  have hv := complex_spectral_summable (-z/2) (edgeValue_summable ha)
    (fun k => ((edgeValue_properties ha).1 k).le)
  have hmass n : (∑' k,‖u n k‖)=‖-z/2‖*(∑' k,jacobi.Jacobi.finiteLambdaAt a b ha hb n k) := by
    simp only [u,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (jacobi.Jacobi.finiteLambdaAt_nonneg ha hb n _),tsum_mul_left]
  have hmassv : (∑' k,‖v k‖)=‖-z/2‖*(1/(2*(a+1))) := by
    simp only [v,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg ((edgeValue_properties ha).1 _).le,tsum_mul_left,first_rayleigh_sum ha]
  have hdiff n : (∑' k,‖u n k-v k‖)=‖-z/2‖*(∑' k,
      |jacobi.Jacobi.finiteLambdaAt a b ha hb n k-edgeValue a ha k|) := by
    simp only [u,v,← mul_sub,← Complex.ofReal_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,tsum_mul_left]
  have ht := (jacobi.Jacobi.finiteLambdaAt_l1_tendsto ha hb).const_mul (C*‖-z/2‖)
  simp only [mul_zero] at ht
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => norm_nonneg _)) ?_ ht
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have h := infinite_product_lipschitz (u n) v (hu n) hv
  rw [hmass n,hmassv,hdiff n] at h
  have hc : Real.exp (‖-z/2‖*(∑' k,jacobi.Jacobi.finiteLambdaAt a b ha hb n k)+
      ‖-z/2‖*(1/(2*(a+1)))) ≤ C := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (jacobi.Jacobi.finiteLambdaAt_trace_bound ha hb hn) (norm_nonneg (-z/2))
    nlinarith only [hh]
  apply h.trans
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right hc (mul_nonneg (norm_nonneg (-z/2))
    (tsum_nonneg (fun k => abs_nonneg _)))


/-- The actual normalized entire Bessel function is its genuine convergent canonical product over all actual squared zeros.
Use: evaluates the logarithmic spectral observables and supplies the exact normalized Weierstrass product in the article.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: the classical Bessel Weierstrass product, proved here from finite Jacobi products and Mehler--Heine.
Proof: choose beta=0. The exact finite Jacobi products converge by the full
L1 spectral limit and also by the genuine complex Mehler--Heine theorem.
Uniqueness of limits identifies the entire functions at every complex point. -/
theorem canonical_product {a : ℝ} (ha : -1<a) (z : ℂ) :
    normalized (a:ℂ) z=∏' k:ℕ,(1-z/(sigma a ha k:ℂ)) := by
  -- The arbitrary complex point includes every spectral zero and the origin.
  have hb : (-1:ℝ)<0 := by norm_num
  have h := finite_canonical_product_tendsto ha hb z
  have he : (fun n : ℕ => ∏' k:ℕ,(1+(-z/2)*(jacobi.Jacobi.finiteLambdaAt a 0 ha hb n k:ℂ)))=ᶠ[atTop]
      fun n : ℕ => jacobi.Jacobi.normalized (a:ℂ) (0:ℂ) n (1-z/(2*(n:ℂ)^2)) := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    exact finite_canonical_product ha hb hn z
  have hmh := (tendstoLocallyUniformlyOn_univ.mpr
    (jacobi.Jacobi.mehler_heine_locallyUniform (a := (a:ℂ)) (b := (0:ℂ)) (by simpa using ha))).tendsto_at (mem_univ z)
  have hid := (tendsto_nhds_unique hmh (h.congr' he))
  rw [hid]
  apply tprod_congr
  intro k
  unfold edgeValue
  push_cast
  ring

end
end jacobi.Bessel
