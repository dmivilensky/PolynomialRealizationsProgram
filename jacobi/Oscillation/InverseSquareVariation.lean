import jacobi.Oscillation.PerturbedMajorant

/-!
Article: jacobi, Proposition B.1.
An actual ordinary derivative bounded by A/x^2+B/N has a bounded total
variation in value on every interval starting beyond one and ending at
O(N). The community mean-value fencing theorem proves this directly,
without an added integrability or continuity hypothesis on the derivative.
Use: supplies the actual comparison function for the finite phase-error integration.
-/
namespace jacobi.Oscillation
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The exact elementary primitive of the uniform corrected-phase majorant has its true ordinary derivative.
Use: supplies the actual comparison function for the finite phase-error integration.
Article: jacobi, Proposition B.1.
Proof: differentiate the literal reciprocal and affine terms and collect the two scalar coefficients. -/
theorem inverseSquare_primitive {a t N : ℝ} (A B : ℝ) (ht : 0<t) :
    HasDerivAt (fun x : ℝ => A*(1/a-1/x)+B*(x-a)/N) (A/t^2+B/N) t := by
  have h1 := ((hasDerivAt_const t (1/a)).sub ((hasDerivAt_id t).inv ht.ne')).const_mul A
  have h2 := (((hasDerivAt_id t).sub_const a).const_mul B).div_const N
  convert h1.add h2 using 1
  · simp only [one_div]; rfl
  · norm_num only [id_eq,mul_one,zero_sub]
    ring

/-- An actual derivative with an inverse-square plus inverse-frequency bound has a uniform integrated value bound on the full growing physical interval.
Use: controls the true difference of finite and Bessel phase invariants without a logarithmic loss.
Article: jacobi, Proposition B.1.
Proof: fence the norm of F(x)-F(a) by the literal primitive of its true
derivative majorant. The initial value is exactly zero. At the terminal
point, 1/a<=1 and x/N<=L bound the two primitive increments uniformly. -/
theorem inverseSquare_variation {F F' : ℝ → ℝ} {a y N A B L : ℝ}
    (ha : 1≤a) (hay : a≤y) (hN : 0<N) (hy : y≤L*N) (hA : 0≤A) (hB : 0≤B)
    (hF : ∀ t∈Icc a y,HasDerivAt F (F' t) t)
    (hbound : ∀ t∈Icc a y,|F' t|≤A/t^2+B/N) :
    |F y-F a|≤A+B*L := by
  -- The norm fencing theorem uses only genuine ordinary derivatives; it does not assume an improper phase integral or an averaged identity.
  have ha0 : 0<a := by linarith
  have hy0 : 0<y := ha0.trans_le hay
  let H := fun t : ℝ => A*(1/a-1/t)+B*(t-a)/N
  have hder : ∀ t∈Icc a y,HasDerivAt H (A/t^2+B/N) t :=
    fun t ht => inverseSquare_primitive A B (ha0.trans_le ht.1)
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (f := fun t => F t-F a) (f' := F') (B := H) (B' := fun t => A/t^2+B/N)
    (fun t ht => ((hF t ht).sub_const (F a)).continuousAt.continuousWithinAt)
    (fun t ht => ((hF t ⟨ht.1,ht.2.le⟩).sub_const (F a)).hasDerivWithinAt)
    (by simp [H])
    (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hder t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt)
    (fun t ht => by simpa only [Real.norm_eq_abs] using hbound t ⟨ht.1,ht.2.le⟩)
    (show y∈Icc a y from ⟨hay,le_rfl⟩)
  rw [Real.norm_eq_abs] at h
  have hrec : 1/a-1/y≤1 := by
    have h1 : 1/a≤1 := div_le_self (by norm_num) ha
    have h2 : 0≤1/y := by positivity
    linarith
  have hlin : (y-a)/N≤L := (div_le_iff₀ hN).mpr (by nlinarith)
  have hbnd : H y≤A+B*L := by
    dsimp [H]
    have hh1 := mul_le_mul_of_nonneg_left hrec hA
    have hh2 := mul_le_mul_of_nonneg_left hlin hB
    rw [← mul_div_assoc] at hh2
    linarith
  exact h.trans hbnd

end
end jacobi.Oscillation
