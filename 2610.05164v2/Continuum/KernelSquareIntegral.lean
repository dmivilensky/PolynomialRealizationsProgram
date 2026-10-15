import «2610.05164v2».Continuum.SpectralMoments
import «2610.05164v2».Continuum.SpectralIdentification

/-!
Article: 2610.05164v2, Theorem 2.4.
The quadratic spectral observation is the literal double integral printed in Section 2.2, for every
nonnegative integrable density.
Use: `«2610.05164v2».Continuum.kernelEigenvalue_square_integral` feeds
`«2610.05164v2».Filters.linear_square_trace` (linear square trace).
-/
namespace «2610.05164v2».Continuum
noncomputable section
open Real Set MeasureTheory
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false

/--
The quadratic spectral observation is the literal double integral printed in Section 2.2, for
every nonnegative integrable density.

Exact identity `(∑' j, kernelEigenvalue hm hn j^2) = ∫ x, ∫ y, m x*m y*exp (-2*|x-y|)`.

Use: `«2610.05164v2».Filters.linear_square_trace` rewrites with this identity to establish
exact identity `(∫ x, (linear hm hn x)^2)=groundParameter hm hn^2/4*(∑' j, kernelEigenvalue hm
hn j^2)`.

Article: 2610.05164v2, Theorem 2.4.

Proof: Identify the summands/integrands on their required domain before replacing the sum or
integral. Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem kernelEigenvalue_square_integral {m : ℝ → ℝ}
    (hm : Integrable m) (hn : ∀ x, 0 ≤ m x) :
    (∑' j, kernelEigenvalue hm hn j^2) =
      ∫ x, ∫ y, m x*m y*exp (-2*|x-y|) := by
  -- Identify the summands/integrands on their required domain before replacing the sum or
  -- integral.
  let T := densityOperator m
  let D := densitySpectralData hm hn
  let : Countable D.Index := orthonormal_countable D.basis.orthonormal
  have hquad (x : ℝ) : HasSum (fun i => D.eig i*inner ℝ (feature x) (D.basis i)^2)
      (inner ℝ (feature x) (T (feature x))) := by
    simpa only [real_inner_comm (D.basis _) (feature x)] using
      eigenbasis_quadratic_hasSum D.basis T D.equation (feature x)
  have hsum (x : ℝ) := (hquad x).mul_left (m x)
  have hb (x : ℝ) : |inner ℝ (feature x) (T (feature x))| ≤ ‖T‖ := by
    calc
      _ ≤ ‖feature x‖*‖T (feature x)‖ := abs_real_inner_le_norm _ _
      _ = ‖T (feature x)‖ := by rw [feature_norm,one_mul]
      _ ≤ ‖T‖ := by simpa only [feature_norm,mul_one] using T.le_opNorm (feature x)
  -- Establish hint as the integrability justification for the later integral estimates or
  -- changes of order.
  have hint : Integrable (fun x => m x*inner ℝ (feature x) (T (feature x))) := by
    apply (hm.norm.mul_const ‖T‖).mono'
    · exact hm.aestronglyMeasurable.mul
        (feature_continuous.inner (T.continuous.comp feature_continuous)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs,abs_mul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)
  have hi := hasSum_integral_of_dominated_convergence
    (F:=fun i x => m x*(D.eig i*inner ℝ (feature x) (D.basis i)^2))
    (f:=fun x => m x*inner ℝ (feature x) (T (feature x))) (μ:=volume)
    (fun i x => m x*(D.eig i*inner ℝ (feature x) (D.basis i)^2))
    (fun i => hm.aestronglyMeasurable.mul
      (aestronglyMeasurable_const.mul ((feature_continuous.inner continuous_const).pow 2).aestronglyMeasurable))
    (fun i => Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hn x) (mul_nonneg (D.nonneg i) (sq_nonneg _)))])
    (Filter.Eventually.of_forall fun x => (hsum x).summable)
    (by
      have he : (fun x => ∑' i, m x*(D.eig i*inner ℝ (feature x) (D.basis i)^2)) =
          (fun x => m x*inner ℝ (feature x) (T (feature x))) := by
        funext x; exact (hsum x).tsum_eq
      rw [he]; exact hint)
    (Filter.Eventually.of_forall hsum)
  have he (i : D.Index) : (∫ x, m x*(D.eig i*inner ℝ (feature x) (D.basis i)^2)) = D.eig i^2 := by
    have hd := D.diagonal_eq i
    rw [densityOperator_inner hm] at hd
    have hfun : (fun x => m x*(D.eig i*inner ℝ (feature x) (D.basis i)^2)) =
        (fun x => D.eig i*(m x*(inner ℝ (feature x) (D.basis i)*inner ℝ (feature x) (D.basis i)))) := by
      funext x; ring
    rw [hfun,integral_const_mul,hd,pow_two]
  simp only [he] at hi
  have hsort := (spectralSorted_moment D.summable D.nonneg (fun a => a^2) (by norm_num)
    (fun a _ => sq_nonneg a) hi.summable).2
  rw [← density_kernel_eigenvalue_eq hm hn D]
  change (∑' j, spectralSorted D.summable j^2) = _
  rw [hsort,hi.tsum_eq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only [T]
    rw [densityOperator_inner hm,← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp only
      rw [feature_inner,← pow_two,← exp_nat_mul,abs_sub_comm]
      rw [show (2:ℕ)*(-|x-y|) = -2*|x-y| by norm_num]
      ring

end
end «2610.05164v2».Continuum
