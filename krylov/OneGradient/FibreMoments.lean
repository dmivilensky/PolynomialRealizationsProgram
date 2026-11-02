import krylov.OneGradient.InformationMoments
import krylov.OneGradient.PhysicalFibre
import krylov.OneGradient.LanczosPower
set_option autoImplicit false
/-!
Article: main_krylov, s5:moment(a).
Use: state the missing-moment theorem for the actual original physical gradient
spectral probability measures on the actual positive last-pivot fibre.
Source: actual spectral-measure polynomial pairings, physical information
invariance and the genuine reconstructed Jacobi coupling product.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Polynomial krylov.Reference
open scoped BigOperators
variable {n : ℕ}

/-- The kth moment of the actual normalized gradient spectral probability measure.
Use: retain the paper's gradient measure rather than substitute the energy measure.
Article: main_krylov, s5:moment(a).
Proof: integrate the monomial over the actual finite positive spectral atoms. -/
def gradientMoment (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) (k : ℕ) : ℝ :=
  ∑ i,(gradientSpectralData A hA g hg).weight i*((gradientSpectralData A hA g hg).node i)^k

/-- The original gradient spectral moments equal the actual normalized physical moments.
Use: transfer the physical information theorem to the original probability measure.
Article: main_krylov, s5:moment(a).
Proof: specialize the genuine polynomial spectral pairing to 1 and X^k and
cancel the strictly positive actual initial norm. -/
theorem gradient_moment_physical (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hg : g≠0) (k : ℕ) :
    gradientMoment A hA g hg k=physicalMoment (cgOperator A) g k := by
  have he := gradientSpectralData_inner A hA g hg 1 (X^k)
  rw [jacobi.Finite.DiscreteMeasure.inner_evaluate] at he
  simp only [CG.polynomialAction,LinearMap.comp_apply,AlgHom.toLinearMap_apply,
    map_one,ContinuousLinearMap.coe_coe,ContinuousLinearMap.apply_apply,one_apply_eq_self,
    map_pow,aeval_X,eval_one,eval_pow,eval_X,mul_one] at he
  unfold physicalMoment gradientMoment
  apply (eq_div_iff (pow_ne_zero 2 (norm_ne_zero_iff.mpr hg))).mpr
  rw [mul_comm]
  exact he.symm

/-- Every genuine positive physical completion has exactly the original gradient
spectral moments through order 2n, where the physical dimension is n+1.
Use: prove the full fixed-moment part on the actual free-last-Jacobi-pivot family.
Article: main_krylov, s5:moment(a), fixed moments through 2N−2.
Proof: the constructed completion preserves the actual old Krylov restriction;
the physical fixed-moment theorem and actual spectral dictionary give the result. -/
theorem fibre_fixed_gradient_moments
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ)
    (hb : (lanczosCompletion A hA g hg hc b).PosDef) (k : ℕ) (hk : k≤2*n) :
    gradientMoment (lanczosCompletion A hA g hg hc b) hb g hg k=gradientMoment A hA g hg k := by
  rw [gradient_moment_physical,gradient_moment_physical]
  exact information_fixed_moments _ _ (cgOperator_positive A hA).1 (cgOperator_positive _ hb).1
    g n (lanczos_completion_information A hA g hg hc b) k hk

/-- The first missing moment is genuinely affine in the last physical Jacobi
pivot with the printed strictly positive squared coupling-product coefficient.
Use: the free moment is derived from the actual original measure and physical
fibre, rather than encoded as an assumed moment-completion parameter.
Article: main_krylov, s5:moment(a), m_(2N−1)=(prod beta)^2*b+c_I.
Proof: apply the genuine physical rank-one missing-moment formula and the exact
last-Lanczos power pairing, then cancel the nonzero actual initial norm. -/
theorem fibre_missing_gradient_moment
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (b : ℝ)
    (hb : (lanczosCompletion A hA g hg hc b).PosDef) :
    let c := ((gradientSpectralData A hA g hg).reconstructed.data.linkProduct n)^2
    gradientMoment (lanczosCompletion A hA g hg hc b) hb g hg (2*n+1)=
      c*b+(gradientMoment A hA g hg (2*n+1)-c*lastJacobiPivot A hA g hg hc) := by
  dsimp only
  rw [gradient_moment_physical,gradient_moment_physical]
  rw [information_first_missing_moment (cgOperator A) _ (cgOperator_positive A hA).1
    (cgOperator_positive _ hb).1 g (lastLanczosVector A hA g hg hc) n
    (b-lastJacobiPivot A hA g hg hc) (lanczos_completion_information A hA g hg hc b)
    (lanczos_completion_operator A hA g hg hc b),last_lanczos_power_pairing]
  field_simp
  ring

end
end krylov.OneGradient
