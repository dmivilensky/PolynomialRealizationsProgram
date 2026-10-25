import polyak.Energy.Values
import polyak.Energy.Symbol
import polyak.Growth.Boundary

/-!
Article: Appendix A, Lemma energy on actual trajectories.
Use: discharge the interpolation, discounting and sampled-value hypotheses for every genuine run.
Proof: the complete table of the actual potential, quadratic homogeneity and exact exponential algebra.
-/

namespace polyak.Energy
noncomputable section
open Interpolation Duality Spectral Growth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Article: fₖ=e⁻ᵏᵗeₖ. Use: the discounted Hilbert position sequence. -/
def discountedPosition (x : ℕ → E) (t : ℝ) (k : ℕ) : E := Real.exp (-(k*t)) • x k

/-- Article: hₖ=e⁻²ᵏᵗψₖ. Use: discounted genuine sampled values. -/
def discountedValue (v : ℕ → ℝ) (t : ℝ) (k : ℕ) : ℝ := Real.exp (-2*k*t)*v k

/-- Article: discounted shift algebra. Use: compensate a lag by its exact exponential factor. -/
theorem exp_mul_discount (t : ℝ) (k n : ℕ) :
    Real.exp (n*t)*Real.exp (-((k+n : ℕ)*t)) = Real.exp (-(k*t)) := by
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

/-- Article: quadratic discount algebra. Use: the square of a first-order discount. -/
theorem exp_discount_sq (t : ℝ) (k : ℕ) : Real.exp (-(k*t))^2 = Real.exp (-2*k*t) := by
  rw [← Real.exp_nat_mul]
  congr 1
  norm_num
  ring

/-- Article: the lagged discounted vector. Use: apply quadratic homogeneity with a common scale. -/
theorem discountedPosition_lag (x : ℕ → E) (t : ℝ) (k n : ℕ) :
    Real.exp (n*t) • discountedPosition x t (k+n) = Real.exp (-(k*t)) • x (k+n) := by
  rw [discountedPosition, smul_smul, exp_mul_discount]

/-- Article: quadratic and value parts of a discounted pair slack. Use: exact equality to actual interpolation. -/
theorem discounted_pair_slack (x σ : ℕ → E) (v : ℕ → ℝ) (t δ : ℝ) (k n : ℕ) :
    pairQuadratic δ (discountedPosition x t k)
      (Real.exp (n*t) • discountedPosition x t (k+n)) (discountedPosition σ t k)
      (Real.exp (n*t) • discountedPosition σ t (k+n)) +
      δ*(Real.exp (2*n*t)*discountedValue v t (k+n)-discountedValue v t k) =
      Real.exp (-2*k*t)*(datumR x σ k (k+n)+δ*datumT x σ v k (k+n)) := by
  have he : Real.exp (2*n*t)*Real.exp (-2*(k+n : ℕ)*t)=Real.exp (-2*k*t) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [discountedPosition_lag, discountedPosition_lag]
  change pairQuadratic δ (Real.exp (-(k*t)) • x k) (Real.exp (-(k*t)) • x (k+n))
    (Real.exp (-(k*t)) • σ k) (Real.exp (-(k*t)) • σ (k+n)) + _ = _
  rw [pairQuadratic_smul, exp_discount_sq, pair_slack_eq]
  unfold discountedValue
  rw [← mul_assoc, he]
  ring

/-- Article: discounted star slack. Use: exact homogeneity including the sampled value. -/
theorem discounted_star_slack (x σ : ℕ → E) (v : ℕ → ℝ) (t δ : ℝ) (k : ℕ) :
    starQuadratic δ (discountedPosition x t k) (discountedPosition σ t k)+
      δ*discountedValue v t k = Real.exp (-2*k*t)*(starQuadratic δ (x k) (σ k)+δ*v k) := by
  unfold discountedPosition discountedValue
  rw [starQuadratic_smul, exp_discount_sq]
  ring

/-- Article: norm of a discounted vector. Use: identify Parseval energy with the plateau energy. -/
theorem norm_discountedPosition_sq (x : ℕ → E) (t : ℝ) (k : ℕ) :
    ‖discountedPosition x t k‖^2 = discountedEnergy x t k := by
  simp only [discountedPosition, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    mul_pow, exp_discount_sq, discountedEnergy]

variable [CompleteSpace E] {A B β : ℝ}

/-- Article: actual discounted interpolation slacks. Use: both certificate signs are genuine inequalities. -/
theorem _root_.polyak.Growth.Run.discounted_pair_nonneg (r : Run E A B β) (t δ : ℝ)
    (hδ : δ=1 ∨ δ= -1) (k n : ℕ) :
    0 ≤ pairQuadratic δ (discountedPosition r.x t k)
      (Real.exp (n*t) • discountedPosition r.x t (k+n))
      (discountedPosition (fun k => gradient r.ψ (r.x k)) t k)
      (Real.exp (n*t) • discountedPosition (fun k => gradient r.ψ (r.x k)) t (k+n)) +
      δ*(Real.exp (2*n*t)*discountedValue (fun k => r.ψ (r.x k)) t (k+n)-
        discountedValue (fun k => r.ψ (r.x k)) t k) := by
  rw [discounted_pair_slack]
  apply mul_nonneg (Real.exp_pos _).le
  have hh := abs_le.mp (r.normalized.tableFeasible r.x k (k+n))
  rcases hδ with rfl | rfl <;> simp only [one_mul, neg_one_mul] <;> linarith [hh.1, hh.2]

/-- Article: actual discounted minimizer inequalities. Use: no value or gradient bound is assumed. -/
theorem _root_.polyak.Growth.Run.discounted_star_nonneg (r : Run E A B β) (t δ : ℝ)
    (hδ : δ=1 ∨ δ= -1) (k : ℕ) :
    0 ≤ starQuadratic δ (discountedPosition r.x t k)
      (discountedPosition (fun k => gradient r.ψ (r.x k)) t k)+
        δ*discountedValue (fun k => r.ψ (r.x k)) t k := by
  rw [discounted_star_slack]
  apply mul_nonneg (Real.exp_pos _).le
  have hh := abs_le.mp ((r.segment k).origin k (by omega))
  change -((1/4 : ℝ)*(‖r.x k‖^2-‖gradient r.ψ (r.x k)‖^2)) ≤
      r.ψ (r.x k)-(1/2 : ℝ)*inner ℝ (gradient r.ψ (r.x k)) (r.x k) ∧
    r.ψ (r.x k)-(1/2 : ℝ)*inner ℝ (gradient r.ψ (r.x k)) (r.x k) ≤
      (1/4 : ℝ)*(‖r.x k‖^2-‖gradient r.ψ (r.x k)‖^2) at hh
  rcases hδ with rfl | rfl <;> unfold starQuadratic <;> linarith [hh.1,hh.2]

/-- Article: Z≥0 on actual trajectories. Use: discharge every local sign hypothesis of the certificate. -/
theorem _root_.polyak.Growth.Run.certificateSlack_nonneg (r : Run E A B β) {m : C(Frequency, ℂ)} {t : ℝ}
    (cert : StrictCertificate m t) (k : ℕ) :
    0 ≤ certificateSlack cert (discountedPosition r.x t)
      (discountedPosition (fun k => gradient r.ψ (r.x k)) t)
      (discountedValue (fun k => r.ψ (r.x k)) t) k := by
  apply polyak.Energy.certificateSlack_nonneg
  · intro n _
    simpa only [one_mul] using r.discounted_pair_nonneg t 1 (Or.inl rfl) k n
  · intro n _
    simpa only [neg_one_mul, ← sub_eq_add_neg] using r.discounted_pair_nonneg t (-1) (Or.inr rfl) k n
  · simpa only [one_mul] using r.discounted_star_nonneg t 1 (Or.inl rfl) k
  · simpa only [neg_one_mul, ← sub_eq_add_neg] using r.discounted_star_nonneg t (-1) (Or.inr rfl) k

/-- Article: actual sampled value estimate. Use: the minimizer datum proves the required half-energy bound. -/
theorem _root_.polyak.Growth.Run.abs_discountedValue_le (r : Run E A B β) (t : ℝ) (k : ℕ) :
    |discountedValue (fun k => r.ψ (r.x k)) t k| ≤ discountedEnergy r.x t k/2 := by
  have hh := abs_value_le_half_sq ((r.segment k).origin k (by omega))
  change |r.ψ (r.x k)| ≤ (1/2 : ℝ)*‖r.x k‖^2 at hh
  unfold discountedValue discountedEnergy
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  nlinarith [mul_le_mul_of_nonneg_left hh (Real.exp_pos (-2*k*t)).le]

/-- Article: integer lift of a discounted trajectory. Use: finite Fourier kernels use integer shifts. -/
def discountedInteger (x : ℕ → E) (t : ℝ) (k : ℤ) : E := discountedPosition x t k.toNat

/-- Article: the actual recurrence eliminates each discounted interior gradient.
Use: identify the precise translation-invariant kernel on every genuine run. -/
theorem _root_.polyak.Growth.Run.filterEval_discountedGradient (r : Run E A B β) (t : ℝ) (hB : B ≠ 0)
    (k : ℕ) (hk : 1 ≤ k) :
    filterEval (gradientFilter A B β t) (discountedInteger r.x t) k =
      discountedPosition (fun k => gradient r.ψ (r.x k)) t k := by
  have hrec := r.recurrence (k-1)
  rw [show k-1+2=k+1 by omega, show k-1+1=k by omega] at hrec
  have he : B • gradient r.ψ (r.x k) = r.x (k+1)-A • r.x k+β • r.x (k-1) := by
    rw [hrec]
    module
  have hs : gradient r.ψ (r.x k) =
      (1/B) • r.x (k+1)-(A/B) • r.x k+(β/B) • r.x (k-1) := by
    calc
      _ = (B⁻¹*B) • gradient r.ψ (r.x k) := by simp [hB]
      _ = B⁻¹ • (B • gradient r.ψ (r.x k)) := by rw [mul_smul]
      _ = _ := by rw [he]; simp only [smul_add, smul_sub, smul_smul]; module
  have hePos : Real.exp t*Real.exp (-((k+1 : ℕ)*t))=Real.exp (-(k*t)) := by
    simpa only [Nat.cast_one, one_mul] using exp_mul_discount t k 1
  have heNeg : Real.exp (-t)*Real.exp (-((k-1 : ℕ)*t))=Real.exp (-(k*t)) := by
    rw [← Real.exp_add]
    congr 1
    rw [Nat.cast_sub hk]
    push_cast
    ring
  rw [filterEval_gradient]
  have hkPos : ((k : ℤ)+1).toNat=k+1 := by omega
  have hkNeg : ((k : ℤ)-1).toNat=k-1 := by omega
  simp only [discountedInteger, Int.toNat_natCast, hkPos, hkNeg, discountedPosition]
  rw [hs]
  simp only [smul_add, smul_sub, smul_smul]
  have hcPos : Real.exp t/B*Real.exp (-((k+1 : ℕ)*t))=Real.exp (-(k*t))*(1/B) := by
    rw [div_eq_mul_inv, mul_right_comm, hePos]
    ring
  have hcNeg : β*Real.exp (-t)/B*Real.exp (-((k-1 : ℕ)*t))=Real.exp (-(k*t))*(β/B) := by
    calc
      _ = (β/B)*(Real.exp (-t)*Real.exp (-((k-1 : ℕ)*t))) := by ring
      _ = _ := by rw [heNeg]; ring
  rw [hcPos,hcNeg]
  module

/-- Article: identification of the actual full quadratic kernel with Q.
Use: all lagged gradients are eliminated using genuine recurrence identities. -/
theorem _root_.polyak.Growth.Run.kernelEval_eq_certificateQuadratic (r : Run E A B β) {m : C(Frequency, ℂ)}
    {t : ℝ} (cert : StrictCertificate m t) (hB : B ≠ 0) (k : ℕ) (hk : 1 ≤ k) :
    kernelEval (certificateKernel A B β t cert) (discountedInteger r.x t) k =
      certificateQuadratic cert (discountedPosition r.x t)
        (discountedPosition (fun k => gradient r.ψ (r.x k)) t) k := by
  rw [kernelEval_certificate]
  have hgrad (n : ℕ) :
      filterEval (gradientFilter A B β t) (discountedInteger r.x t) ((k : ℤ)+n) =
        discountedPosition (fun k => gradient r.ψ (r.x k)) t (k+n) := by
    simpa only [Nat.cast_add] using r.filterEval_discountedGradient t hB (k+n) (by omega)
  simp only [r.filterEval_discountedGradient t hB k hk, hgrad, discountedInteger,
    Int.toNat_natCast, Int.toNat_add_nat (by omega : (0 : ℤ) ≤ k), certificateQuadratic]

end
end polyak.Energy
