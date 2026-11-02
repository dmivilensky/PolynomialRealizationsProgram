import jacobi.Support.SineProductCorrection

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
The arbitrary-shift log-sinc correction has a quantitative uniform
finite-mesh error. Reusing the C2 log-sinc theory from chebyshev1
avoids a separate Riemann-sum argument and applies equally to the
original step and its half step.
Use: sineCorrection_error sums this estimate for the actual log-sinc correction at every original support mesh cell.
-/
namespace jacobi.Support
noncomputable section
open Real Set Finset chebyshev1.SineJacobi

/-- A shifted smooth mesh increment differs from its linear multiple of the unit increment by a uniform quadratic error.
Use: sineCorrection_error sums this estimate for the actual log-sinc correction at every original support mesh cell.
Article: jacobi, Appendix C.3 (top-node polynomials).
Source: Taylor's first-order remainder, reusing chebyshev1.Analysis.first_order_error_bound.
Proof: subtract the two Taylor remainders based at the same left endpoint; their linear terms cancel exactly. -/
theorem smooth_shift_error {f f' f'' : ℝ→ℝ} {b M x q s : ℝ}
    (hM:0≤M) (hx:0≤x) (hq:0≤q) (hs:0≤s)
    (hxs:x+s*q≤b) (hxq:x+q≤b)
    (hf:∀t∈Icc 0 b,HasDerivAt f (f' t) t)
    (hf':∀t∈Icc 0 b,HasDerivAt f' (f'' t) t)
    (hbnd:∀t∈Icc 0 b,|f'' t|≤M) :
    |f (x+s*q)-f (x+q)-(s-1)*(f (x+q)-f x)|≤M*(s^2+s)*q^2 := by
  -- The same Taylor base makes the arbitrary nonintegral shift as simple as a unit mesh increment.
  have hab : x≤b := le_trans (le_add_of_nonneg_right hq) hxq
  have hsub : Icc x b⊆Icc 0 b := fun t ht => ⟨hx.trans ht.1,ht.2⟩
  have hT (r : ℝ) (hr:0≤r) (hxr:x+r*q≤b) :=
    chebyshev1.Analysis.first_order_error_bound hab
      (show x+r*q∈Icc x b from ⟨le_add_of_nonneg_right (mul_nonneg hr hq),hxr⟩) hM
      (fun t ht => hf t (hsub ht)) (fun t ht => hf' t (hsub ht)) (fun t ht => hbnd t (hsub ht))
  have h0 := hT s hs hxs
  have h1 := hT 1 (by norm_num) (by simpa using hxq)
  have he : f (x+s*q)-f (x+q)-(s-1)*(f (x+q)-f x)=
      (f (x+s*q)-f x-f' x*(x+s*q-x))-s*(f (x+q)-f x-f' x*(x+q-x)) := by ring
  rw [he]
  calc
    _ ≤ |f (x+s*q)-f x-f' x*(x+s*q-x)|+|s*(f (x+q)-f x-f' x*(x+q-x))| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le
        (f (x+s*q)-f x-f' x*(x+s*q-x)) (s*(f (x+q)-f x-f' x*(x+q-x)))
    _ ≤ M*(x+s*q-x)^2+s*(M*(x+q-x)^2) := by
      rw [abs_mul,abs_of_nonneg hs]
      exact add_le_add h0 (mul_le_mul_of_nonneg_left (by simpa using h1) hs)
    _ = _ := by ring

/-- The genuine arbitrary-shift support sine-product correction has a uniform error bounded by an explicit constant times m/N^2.
Use: the source's uniform sine-product power law and normalized limit follow by combining this actual finite estimate with the already proved Gamma quotient limit.
Article: jacobi, Appendix C.3 (sine-product estimates).
Proof: the existing log-sinc C2 theorem supplies both actual derivatives and a uniform second-derivative bound on the fixed compact interval. Sum the proved mesh-cell Taylor estimate, then telescope the unit increments from logSinc(0)=0. -/
theorem sineCorrection_error {b : ℝ} (hb:0≤b) (hb1:b<1) :
    ∃M:ℝ,0≤M ∧ ∀N s:ℝ,0<N→0≤s→∀m:ℕ,
      (∀j<m,((j:ℝ)+s)/N≤b ∧ ((j:ℝ)+1)/N≤b)→
      |sineCorrection N s m-(s-1)*logSinc ((m:ℝ)/N)|≤M*(s^2+s)*(m:ℝ)/N^2 := by
  -- The analytic constant comes from the earlier article's actual smooth log-sinc function.
  obtain ⟨M,hM,hbnd⟩ := logSinc_second_bound hb hb1
  have hsub : Icc (0:ℝ) b⊆Ioo (-1:ℝ) 1 := fun x hx => ⟨by linarith [hx.1],hx.2.trans_lt hb1⟩
  have hg : ∀x∈Icc (0:ℝ) b,HasDerivAt logSinc (deriv logSinc x) x := by
    intro x hx
    exact ((logSinc_contDiff.differentiableOn (by norm_num) x (hsub hx)).differentiableAt
      (isOpen_Ioo.mem_nhds (hsub hx))).hasDerivAt
  have hg' : ∀x∈Icc (0:ℝ) b,HasDerivAt (deriv logSinc) (deriv (deriv logSinc) x) x := by
    intro x hx
    have h1 : ContDiffOn ℝ 1 (deriv logSinc) (Ioo (-1:ℝ) 1) :=
      logSinc_contDiff.deriv_of_isOpen isOpen_Ioo (by norm_num)
    exact ((h1.differentiableOn (by norm_num) x (hsub hx)).differentiableAt
      (isOpen_Ioo.mem_nhds (hsub hx))).hasDerivAt
  refine ⟨M,hM,?_⟩
  intro N s hN hs m hmesh
  let E : ℕ→ℝ := fun j => logSinc (((j:ℝ)+s)/N)-logSinc (((j:ℝ)+1)/N)-
    (s-1)*(logSinc (((j:ℝ)+1)/N)-logSinc ((j:ℝ)/N))
  have he : sineCorrection N s m-(s-1)*logSinc ((m:ℝ)/N)=∑j∈range m,E j := by
    dsimp [sineCorrection,E]
    simp only [sum_sub_distrib,← mul_sum]
    have ht := sum_range_sub (fun j => logSinc ((j:ℝ)/N)) m
    simp only [Nat.cast_zero,zero_div,logSinc_zero,sub_zero,Nat.cast_add,Nat.cast_one] at ht
    rw [sum_sub_distrib] at ht
    rw [ht]
  rw [he]
  calc
    _ ≤ ∑j∈range m,|E j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑_j∈range m,M*(s^2+s)/N^2 := by
      apply sum_le_sum
      intro j hj
      have hj' := mem_range.mp hj
      have hcell := smooth_shift_error hM (div_nonneg (Nat.cast_nonneg j) hN.le)
        (inv_nonneg.mpr hN.le) hs
        (by convert (hmesh j hj').1 using 1; ring)
        (by convert (hmesh j hj').2 using 1; ring) hg hg' hbnd
      dsimp [E]
      simpa only [div_eq_mul_inv,add_mul,one_mul,inv_pow] using hcell
    _ = _ := by simp only [sum_const,nsmul_eq_mul,card_range]; ring

end
end jacobi.Support
