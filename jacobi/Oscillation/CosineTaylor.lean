import jacobi.Oscillation.PhaseMeanValue

/-!
Article: jacobi, Proposition B.1.
The actual cosine has its global first-order Taylor bound with the sharp
quadratic remainder. The proof uses the community sine Lipschitz bound
and the genuine derivative fencing theorem on the unit segment.
Source: the elementary Taylor estimate for a function with one-Lipschitz derivative.
Use: converts the actual sharp angular expansion and coarse displacement into the original corrected cosine-node error in Proposition B.1 (b).
-/
namespace jacobi.Oscillation
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The true cosine linearization has its sharp global quadratic remainder at every real displacement.
Use: converts the actual sharp angular expansion and coarse displacement into the original corrected cosine-node error in Proposition B.1 (b).
Article: jacobi, Proposition B.1.
Proof: parametrize the actual displacement by t in [0,1]. The true
remainder derivative is d*(sin(x)-sin(x+t*d)), bounded by d^2*t using
the community sine Lipschitz theorem. Fence its actual primitive d^2*t^2/2. -/
theorem cosine_linear_remainder (x d : ℝ) :
    |cos (x+d)-cos x+d*sin x|≤d^2/2 := by
  -- Parametrization by the unit interval handles both signs of the original angular displacement in one proof.
  let F := fun t : ℝ => cos (x+t*d)-cos x+(t*d)*sin x
  have hder : ∀ t,HasDerivAt F (d*(sin x-sin (x+t*d))) t := by
    intro t
    have harg := ((hasDerivAt_id t).mul_const d).const_add x
    convert ((harg.cos.sub_const (cos x)).add (((hasDerivAt_id t).mul_const d).mul_const (sin x))) using 1
    · rfl
    · dsimp only [id_eq]
      ring
  have hB : ∀ t : ℝ,HasDerivAt (fun u => d^2*u^2/2) (d^2*t) t := by
    intro t
    convert (((hasDerivAt_id t).pow 2).const_mul (d^2)).div_const 2 using 1
    · rfl
    · norm_num only [id_eq,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
      ring
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (a := 0) (b := 1) (f := F) (f' := fun t => d*(sin x-sin (x+t*d)))
    (fun t _ => (hder t).continuousAt.continuousWithinAt)
    (fun t _ => (hder t).hasDerivWithinAt) (B := fun t => d^2*t^2/2)
    (by simp [F]) hB (by
      intro t ht
      rw [Real.norm_eq_abs,abs_mul]
      have hh := Real.abs_sin_sub_sin_le x (x+t*d)
      have he : |x-(x+t*d)|=t*|d| := by
        rw [show x-(x+t*d)= -(t*d) by ring,abs_neg,abs_mul,abs_of_nonneg ht.1]
      rw [he] at hh
      have hm := mul_le_mul_of_nonneg_left hh (abs_nonneg d)
      convert hm using 1
      rw [show |d| *(t*|d|)=t*|d|^2 by ring,sq_abs]
      ring) (show (1:ℝ)∈Icc 0 1 by constructor <;> norm_num)
  simpa only [F,one_mul,one_pow,mul_one,Real.norm_eq_abs] using h

end
end jacobi.Oscillation
