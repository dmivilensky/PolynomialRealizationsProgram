import jacobi.Reference.GammaProduct

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Euler's limit identifies the genuinely convergent symmetric product
with the literal reciprocal-Gamma characteristic. The argument includes
its zeros, where one original factor vanishes; it never divides by a
zero Gamma value or drops a possible entire normalization factor.
Use: supplies the fully normalized characteristicTau_product below.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The symmetric Gamma product has its exact original value at every complex argument, including all zeros.
Use: supplies the fully normalized characteristicTau_product below.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: Euler's Gamma limit formula, proved in mathlib.
Proof: if a Gamma denominator is a pole, the corresponding genuine
product factor is zero. Otherwise the exact finite identity and the
community Euler limits give the result by uniqueness of limits; absolute
product convergence was established independently before this passage. -/
theorem gamma_symmetric_product {g : ℝ} (hg : 0<g) (x : ℂ) :
    (∏' k : ℕ,(1-x^2/((k:ℂ)+(g:ℂ))^2))=
      (Complex.Gamma (g:ℂ))^2/
        (Complex.Gamma ((g:ℂ)-x)*Complex.Gamma ((g:ℂ)+x)) := by
  -- Pole cases are actual zero factors; Euler's quotient limit is used only with nonzero limiting denominators.
  by_cases hm : Complex.Gamma ((g:ℂ)-x)=0
  · obtain ⟨k,hk⟩ := (Complex.Gamma_eq_zero_iff _).mp hm
    have hx : x=(k:ℂ)+(g:ℂ) := by linear_combination -hk
    have hbase : (k:ℂ)+(g:ℂ)≠0 := by
      have hpos : 0<((k:ℂ)+(g:ℂ)).re := by
        simpa using add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) hg
      intro hz; rw [hz,zero_re] at hpos; exact lt_irrefl _ hpos
    rw [tprod_of_exists_eq_zero ⟨k,by rw [hx,div_self (pow_ne_zero 2 hbase),sub_self]⟩,
      hm,zero_mul,div_zero]
  by_cases hp : Complex.Gamma ((g:ℂ)+x)=0
  · obtain ⟨k,hk⟩ := (Complex.Gamma_eq_zero_iff _).mp hp
    have hx : x= -((k:ℂ)+(g:ℂ)) := by linear_combination hk
    have hbase : (k:ℂ)+(g:ℂ)≠0 := by
      have hpos : 0<((k:ℂ)+(g:ℂ)).re := by
        simpa using add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) hg
      intro hz; rw [hz,zero_re] at hpos; exact lt_irrefl _ hpos
    rw [tprod_of_exists_eq_zero ⟨k,by rw [hx,neg_sq,div_self (pow_ne_zero 2 hbase),sub_self]⟩,
      hp,mul_zero,div_zero]
  have hP := (gamma_symmetric_multipliable hg x).tendsto_prod_tprod_nat.comp (tendsto_add_atTop_nat 1)
  have hG := ((Complex.GammaSeq_tendsto_Gamma (g:ℂ)).pow 2).div
    ((Complex.GammaSeq_tendsto_Gamma ((g:ℂ)-x)).mul
      (Complex.GammaSeq_tendsto_Gamma ((g:ℂ)+x))) (mul_ne_zero hm hp)
  have he : (fun n : ℕ => ∏ k∈Finset.range (n+1),(1-x^2/((k:ℂ)+(g:ℂ))^2))=ᶠ[atTop]
      (fun n => (Complex.GammaSeq (g:ℂ) n)^2/
        (Complex.GammaSeq ((g:ℂ)-x) n*Complex.GammaSeq ((g:ℂ)+x) n)) := by
    filter_upwards [eventually_ne_atTop (0:ℕ)] with n hn
    exact gamma_symmetric_finite hg x hn hm hp
  exact tendsto_nhds_unique (hP.congr' he) hG

/-- The literal reference characteristic equals the genuinely convergent Euler product with exactly its printed Gamma prefactor.
Use: supplies the source characteristic comparison and subsequent norming-product and parity calculations.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: substitute x=omega/pi in the proved symmetric Gamma product.
The exact frequency square replaces omega^2 by z-c_0. The genuine
positive Gamma(gamma) fixes the original central normalization. -/
theorem characteristicTau_product {a : ℝ} (ha : -1<a) (z : ℂ) :
    characteristicTau a z=(Complex.Gamma (gamma a:ℂ)^2)⁻¹*
      ∏' k : ℕ,((eigenvalue a k:ℂ)-z)/
        ((Real.pi:ℂ)^2*((k:ℂ)+(gamma a:ℂ))^2) := by
  -- Both the product's convergence and its normalizing constant have already been fixed independently.
  let w := Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))
  let x := w/(Real.pi:ℂ)
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  have hG : Complex.Gamma (gamma a:ℂ)≠0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hg)
  have he (k : ℕ) : (1-x^2/((k:ℂ)+(gamma a:ℂ))^2)=
      ((eigenvalue a k:ℂ)-z)/((Real.pi:ℂ)^2*((k:ℂ)+(gamma a:ℂ))^2) := by
    have hk : (k:ℂ)+(gamma a:ℂ)≠0 := by
      have hpos : 0<((k:ℂ)+(gamma a:ℂ)).re := by
        simpa using add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) hg
      intro hz; rw [hz,zero_re] at hpos; exact lt_irrefl _ hpos
    dsimp [x]
    rw [div_pow]
    have hw : w^2=z-(jacobi.Jacobi.endpointCorrection a:ℂ) := frequency_square _
    rw [hw]
    unfold eigenvalue
    push_cast
    field_simp [hk,Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    ring
  rw [← tprod_congr he,gamma_symmetric_product hg x]
  change characteristicGamma a x=(Complex.Gamma (gamma a:ℂ)^2)⁻¹*
    (Complex.Gamma (gamma a:ℂ)^2/
      (Complex.Gamma ((gamma a:ℂ)-x)*Complex.Gamma ((gamma a:ℂ)+x)))
  rw [div_eq_mul_inv,← mul_assoc,inv_mul_cancel₀ (pow_ne_zero 2 hG),one_mul,
    mul_inv,characteristicGamma]

end
end jacobi.Reference
