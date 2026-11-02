import jacobi.Reference.RelativeCharacteristic
import jacobi.Complex.AffineProduct

/-!
Article: jacobi, Proposition C.3.
The genuine complex derivatives of the original printed characteristics
at their actual spectral zeros are their original omitted-factor
canonical products. These identities connect the defining spectral
gap product rho_k with the original characteristic derivative ratio.
Use: the actual Bessel characteristic is an absolutely convergent affine product whose root derivative is computed below.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The true reciprocal Bessel spectrum is absolutely summable as a complex weight sequence.
Use: the actual Bessel characteristic is an absolutely convergent affine product whose root derivative is computed below.
Article: jacobi, Proposition C.3.
Proof: its norm is one half of the original positive edge eigenvalue sequence, whose first trace was already proved summable. -/
theorem inverse_sigma_summable {a : ℝ} (ha : -1<a) :
    Summable (fun k : ℕ => ‖(jacobi.Bessel.sigma a ha k:ℂ)⁻¹‖) := by
  convert! (jacobi.Bessel.edgeValue_summable ha).mul_left (1/2:ℝ) using 1
  funext k
  rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha k))]
  unfold jacobi.Bessel.edgeValue
  ring

/-- The true reciprocal reference squared phases are absolutely summable as complex weights.
Use: differentiates the actual original reference canonical product, whose denominators remain positive even if a reference eigenvalue is zero.
Article: jacobi, Proposition C.3.
Proof: its norm is the original shifted reciprocal-square series times pi^(-2), proved summable in GammaProduct. -/
theorem inverse_phase_summable {a : ℝ} (ha : -1<a) :
    Summable (fun k : ℕ => ‖((Real.pi:ℂ)^2*((k:ℂ)+(gamma a:ℂ))^2)⁻¹‖) := by
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  convert! (shifted_inverse_square_summable hg).mul_left (1/Real.pi^2) using 1
  funext k
  rw [norm_inv,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,
    show (k:ℂ)+(gamma a:ℂ)=(((k:ℝ)+gamma a:ℝ):ℂ) by push_cast; rfl,
    norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (show 0<(k:ℝ)+gamma a by positivity)]
  simp only [mul_inv,one_div]

/-- The original printed Bessel characteristic derivative equals its genuine omitted-factor product at every true Bessel spectral zero.
Use: compares with characteristicTau_derivative_product to identify the original defining rho product with the actual derivative ratio.
Article: jacobi, Proposition C.3.
Proof: the original canonical product is an absolutely convergent
affine product with true weights 1/sigma_l. Its kth factor vanishes
at the actual sigma_k. The genuine simple-factor derivative theorem
therefore applies; its omitted factors and original scalar are kept. -/
theorem characteristicSigma_derivative_product {a : ℝ} (ha : -1<a) (k : ℕ) :
    deriv (characteristicSigma a) (jacobi.Bessel.sigma a ha k:ℂ)=
      -(characteristicSigmaConstant a:ℂ)/(jacobi.Bessel.sigma a ha k:ℂ)*
        ∏' l : ℕ,if l=k then 1 else
          ((jacobi.Bessel.sigma a ha l:ℂ)-(jacobi.Bessel.sigma a ha k:ℂ))/(jacobi.Bessel.sigma a ha l:ℂ) := by
  classical
  -- The derivative is taken of the original printed entire characteristic, after its exact product has been identified.
  let w : ℕ → ℂ := fun l => (jacobi.Bessel.sigma a ha l:ℂ)⁻¹
  have hσ (l : ℕ) : (jacobi.Bessel.sigma a ha l:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
    (jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha l)).ne'
  have hroot : 1+((0:ℂ)-(jacobi.Bessel.sigma a ha k:ℂ))*w k=0 := by dsimp [w]; field_simp [hσ k]; ring
  have hd := (jacobi.Complex.affine_product_derivative_at_zero (inverse_sigma_summable ha) 0
    (jacobi.Bessel.sigma a ha k:ℂ) k hroot).const_mul (characteristicSigmaConstant a:ℂ)
  have hf : (fun z : ℂ => (characteristicSigmaConstant a:ℂ)*
      ∏' l : ℕ,(1+((0:ℂ)-z)*(jacobi.Bessel.sigma a ha l:ℂ)⁻¹))=characteristicSigma a := by
    funext z
    rw [characteristicSigma,jacobi.Bessel.canonical_product ha]
    congr 1
    apply tprod_congr
    intro l
    ring
  rw [hf] at hd
  rw [hd.deriv]
  have hp : (∏' l : ℕ,if l=k then 1 else 1+((0:ℂ)-(jacobi.Bessel.sigma a ha k:ℂ))*(jacobi.Bessel.sigma a ha l:ℂ)⁻¹)=
      ∏' l : ℕ,if l=k then 1 else
        ((jacobi.Bessel.sigma a ha l:ℂ)-(jacobi.Bessel.sigma a ha k:ℂ))/(jacobi.Bessel.sigma a ha l:ℂ) := by
    apply tprod_congr
    intro l
    split_ifs
    · rfl
    · field_simp [hσ l]; ring
  rw [hp]
  ring

/-- The original printed reference characteristic derivative equals its genuine omitted-factor product at every original reference spectral zero.
Use: identifies the source rho product by comparison with characteristicSigma_derivative_product and the already proved original normalization product.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: the true affine-product weights are reciprocal squared
reference phases, not reciprocal reference eigenvalues. They are
summable and nonzero for every original index, including when tau_k
itself is zero. The actual kth affine factor vanishes exactly there. -/
theorem characteristicTau_derivative_product {a : ℝ} (ha : -1<a) (k : ℕ) :
    deriv (characteristicTau a) (eigenvalue a k:ℂ)=
      -(Complex.Gamma (gamma a:ℂ)^2)⁻¹/((Real.pi:ℂ)^2*((k:ℂ)+(gamma a:ℂ))^2)*
        ∏' l : ℕ,if l=k then 1 else
          ((eigenvalue a l:ℂ)-(eigenvalue a k:ℂ))/((Real.pi:ℂ)^2*((l:ℂ)+(gamma a:ℂ))^2) := by
  classical
  -- The original positive phases supply the actual affine weights independently of the signs of the reference energies.
  let w : ℕ → ℂ := fun l => ((Real.pi:ℂ)^2*((l:ℂ)+(gamma a:ℂ))^2)⁻¹
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  have hw (l : ℕ) : (Real.pi:ℂ)^2*((l:ℂ)+(gamma a:ℂ))^2≠0 := by
    apply mul_ne_zero (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    apply pow_ne_zero
    exact_mod_cast (ne_of_gt (show 0<(l:ℝ)+gamma a by positivity))
  have he (z : ℂ) (l : ℕ) : 1+((jacobi.Jacobi.endpointCorrection a:ℂ)-z)*w l=
      ((eigenvalue a l:ℂ)-z)/((Real.pi:ℂ)^2*((l:ℂ)+(gamma a:ℂ))^2) := by
    unfold eigenvalue
    dsimp [w]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero,
      show (l:ℂ)+(gamma a:ℂ)≠0 by exact_mod_cast (ne_of_gt (show 0<(l:ℝ)+gamma a by positivity))]
    ring
  have hroot : 1+((jacobi.Jacobi.endpointCorrection a:ℂ)-(eigenvalue a k:ℂ))*w k=0 := by
    rw [he,sub_self,zero_div]
  have hd := (jacobi.Complex.affine_product_derivative_at_zero (inverse_phase_summable ha)
    (jacobi.Jacobi.endpointCorrection a:ℂ) (eigenvalue a k:ℂ) k hroot).const_mul
      (Complex.Gamma (gamma a:ℂ)^2)⁻¹
  have hf : (fun z : ℂ => (Complex.Gamma (gamma a:ℂ)^2)⁻¹*
      ∏' l : ℕ,(1+((jacobi.Jacobi.endpointCorrection a:ℂ)-z)*w l))=characteristicTau a := by
    funext z
    rw [characteristicTau_product ha]
    congr 1
    apply tprod_congr
    exact he z
  change HasDerivAt (fun z : ℂ => (Complex.Gamma (gamma a:ℂ)^2)⁻¹*
    ∏' l : ℕ,(1+((jacobi.Jacobi.endpointCorrection a:ℂ)-z)*w l)) _ (eigenvalue a k:ℂ) at hd
  rw [hf] at hd
  rw [hd.deriv]
  have hp : (∏' l : ℕ,if l=k then 1 else 1+((jacobi.Jacobi.endpointCorrection a:ℂ)-(eigenvalue a k:ℂ))*w l)=
      ∏' l : ℕ,if l=k then 1 else
        ((eigenvalue a l:ℂ)-(eigenvalue a k:ℂ))/((Real.pi:ℂ)^2*((l:ℂ)+(gamma a:ℂ))^2) := by
    apply tprod_congr
    intro l
    split_ifs
    · rfl
    · exact he _ l
  rw [hp]
  ring

end
end jacobi.Reference
