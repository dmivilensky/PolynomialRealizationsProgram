import jacobi.Reference.CharacteristicGamma
import jacobi.Bessel.SpectralBounds
import Mathlib.Analysis.Normed.Ring.InfiniteProd

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The symmetric Gamma product is obtained from the community Euler limit
formula. Its exponential and factorial factors cancel at every finite
stage. Absolute convergence of the remaining inverse-square product is
proved before its limit is interpreted.
Source: Euler's Gamma limit formula, Complex.GammaSeq_tendsto_Gamma.
Use: proves absolute convergence of the reference characteristic product in gamma_symmetric_product.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The original positive shifted-index reciprocal squares are summable, including the full finite prefix.
Use: proves absolute convergence of the reference characteristic product in gamma_symmetric_product.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: min(1,gamma)*(k+1)<=k+gamma gives one inverse-square majorant throughout the original positive parameter range. -/
theorem shifted_inverse_square_summable {g : ℝ} (hg : 0<g) :
    Summable (fun k : ℕ => 1/((k:ℝ)+g)^2) := by
  -- A strictly positive lower coefficient handles the original index zero as well as the tail.
  let c := min 1 g
  have hc : 0<c := lt_min zero_lt_one hg
  have hbase (k : ℕ) : c*(k+1:ℝ)≤(k:ℝ)+g := by
    have h1 : c≤1 := min_le_left _ _
    have h2 : c≤g := min_le_right _ _
    have hh := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg (α := ℝ) k)
    nlinarith
  have hs := (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left (1/c^2)
  simp only [one_pow] at hs
  apply hs.of_nonneg_of_le (fun _ => by positivity)
  intro k
  have hk : 0<(k:ℝ)+g := by positivity
  have hkp : 0<(k+1:ℝ) := by positivity
  have hh := (sq_le_sq₀ (mul_nonneg hc.le hkp.le) hk.le).mpr (hbase k)
  apply (div_le_iff₀ (sq_pos_of_pos hk)).mpr
  field_simp [hc.ne',hkp.ne']
  nlinarith

/-- Every symmetric reference Gamma product converges absolutely as a genuine complex product.
Use: the finite Euler-Gamma limit uniquely determines the product value, even when an actual factor vanishes.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: each factor deviation has norm |x^2|/(k+gamma)^2, whose original inverse-square series is summable. -/
theorem gamma_symmetric_multipliable {g : ℝ} (hg : 0<g) (x : ℂ) :
    Multipliable (fun k : ℕ => 1-x^2/((k:ℂ)+(g:ℂ))^2) := by
  -- The actual factor deviations are bounded by one convergent real series before forming any totalized product.
  have hs := (shifted_inverse_square_summable hg).mul_left ‖x^2‖
  have hn : Summable (fun k : ℕ => ‖-x^2/((k:ℂ)+(g:ℂ))^2‖) := by
    convert hs using 1
    funext k
    rw [norm_div,norm_neg,norm_pow]
    rw [show (k:ℂ)+(g:ℂ)=(((k:ℝ)+g:ℝ):ℂ) by push_cast; rfl,
      norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(k:ℝ)+g)]
    ring
  have he : (fun k : ℕ => 1+(-x^2/((k:ℂ)+(g:ℂ))^2))=
      (fun k : ℕ => 1-x^2/((k:ℂ)+(g:ℂ))^2) := by funext k; ring
  rw [← he]
  exact multipliable_one_add_of_summable hn

/-- At every finite stage Euler's Gamma approximants have exactly the symmetric characteristic product, without an exponential factor.
Use: passes the community Gamma limit through the original finite products in gamma_symmetric_product.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: multiply the two numerator factors at each index to obtain
(k+gamma)^2-x^2. The equal total complex exponents cancel, as do the
two genuine nonzero factorials; no limiting asymptotic is invoked. -/
theorem gamma_symmetric_finite {g : ℝ} (hg : 0<g) (x : ℂ) {n : ℕ} (hn : n≠0)
    (hm : Complex.Gamma ((g:ℂ)-x)≠0) (hp : Complex.Gamma ((g:ℂ)+x)≠0) :
    (∏ k∈Finset.range (n+1),(1-x^2/((k:ℂ)+(g:ℂ))^2))=
      (Complex.GammaSeq (g:ℂ) n)^2/
        (Complex.GammaSeq ((g:ℂ)-x) n*Complex.GammaSeq ((g:ℂ)+x) n) := by
  -- Keep the original finite products visible until all actual nonzero factors are established.
  have hnon {u : ℂ} (hu : Complex.Gamma u≠0) (j : ℕ) : u+(j:ℂ)≠0 := by
    intro h
    exact hu ((Complex.Gamma_eq_zero_iff _).mpr ⟨j,eq_neg_of_add_eq_zero_left h⟩)
  have hPg : (∏ j∈Finset.range (n+1),((g:ℂ)+(j:ℂ)))≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => hnon
      (Complex.Gamma_ne_zero_of_re_pos (by simpa using hg)) j)
  have hPm : (∏ j∈Finset.range (n+1),((g:ℂ)-x+(j:ℂ)))≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => hnon hm j)
  have hPp : (∏ j∈Finset.range (n+1),((g:ℂ)+x+(j:ℂ)))≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => hnon hp j)
  have hprod : (∏ k∈Finset.range (n+1),(1-x^2/((k:ℂ)+(g:ℂ))^2))=
      ((∏ j∈Finset.range (n+1),((g:ℂ)-x+(j:ℂ)))*
        (∏ j∈Finset.range (n+1),((g:ℂ)+x+(j:ℂ))))/
          (∏ j∈Finset.range (n+1),((g:ℂ)+(j:ℂ)))^2 := by
    rw [← Finset.prod_mul_distrib,← Finset.prod_pow,← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro j _
    have hj : (j:ℂ)+(g:ℂ)≠0 := by
      have hre : 0<((j:ℂ)+(g:ℂ)).re := by simpa using add_pos_of_nonneg_of_pos (Nat.cast_nonneg j) hg
      intro h; rw [h,zero_re] at hre; exact lt_irrefl _ hre
    rw [add_comm (g:ℂ) (j:ℂ)]
    field_simp [hj]
    ring
  have hnc : (n:ℂ)≠0 := Nat.cast_ne_zero.mpr hn
  have hnf : (n.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hng : (n:ℂ)^(g:ℂ)≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hnc)
  have hnm : (n:ℂ)^((g:ℂ)-x)≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hnc)
  have hnp : (n:ℂ)^((g:ℂ)+x)≠0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hnc)
  have he : (n:ℂ)^((g:ℂ)-x)*(n:ℂ)^((g:ℂ)+x)=((n:ℂ)^(g:ℂ))^2 := by
    rw [← Complex.cpow_add _ _ hnc,pow_two,← Complex.cpow_add _ _ hnc]
    congr 1
    ring
  rw [hprod,Complex.GammaSeq,Complex.GammaSeq,Complex.GammaSeq]
  field_simp [hPg,hPm,hPp,hnf,hng,hnm,hnp]
  exact he

end
end jacobi.Reference
