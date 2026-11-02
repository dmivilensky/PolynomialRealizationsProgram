import jacobi.Support.SineShiftBounds

/-!
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Source: the elementary positive reduction-of-order Green formula.
Use: Support.volterraKernel_linear discharges every input using the actual support polynomial, its proved growth and genuine positive matrix couplings. The resulting bound gives uniform complex wave estimates and a bounded dominating function in the support edge limit.
-/
namespace jacobi.Finite
noncomputable section
open Real Finset

/-- A genuine positive reduction-of-order kernel is bounded by a linear Volterra kernel after its original monotone growth weight is applied.
Use: Support.volterraKernel_linear discharges every input using the actual support polynomial, its proved growth and genuine positive matrix couplings. The resulting bound gives uniform complex wave estimates and a bounded dominating function in the support edge limit.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: for every original summation index l>=j, both genuine reference values are at least c*w_j by monotonicity of the actual weight. Thus every original reciprocal summand is at most 1/(A*c^2*w_j^2). Count the actual finite interval, apply the two original endpoint upper bounds and cancel only the genuine positive weights. -/
theorem reduction_kernel_linear (u a w : ℕ→ℝ) (N : ℕ) {c C A : ℝ}
    (hc:0<c) (hC:0<C) (hA:0<A) (hw:∀r≤N,0<w r)
    (hwmono:∀r s,r≤s→s≤N→w r≤w s)
    (hu:∀r≤N,c*w r≤u r ∧ u r≤C*w r) (ha:∀r<N,A≤a (r+1))
    {m j : ℕ} (hm:m≤N) (hj:j≤m) :
    (u m*u j*∑r∈Ico j m,(a (r+1)*u r*u (r+1))⁻¹)*w j/w m≤
      (C^2/(A*c^2))*((m-j:ℕ):ℝ) := by
  -- The same original lower reference value at j controls every actual later reciprocal factor.
  have hwj := hw j (hj.trans hm)
  have hwm := hw m hm
  have hum0 : 0≤u m := (mul_pos hc hwm).le.trans (hu m hm).1
  have huj0 : 0≤u j := (mul_pos hc hwj).le.trans (hu j (hj.trans hm)).1
  have hbase : 0<A*c^2*(w j)^2 := by positivity
  have hs : (∑r∈Ico j m,(a (r+1)*u r*u (r+1))⁻¹)≤
      ((m-j:ℕ):ℝ)*(A*c^2*(w j)^2)⁻¹ := by
    calc
      _ ≤ ∑_r∈Ico j m,(A*c^2*(w j)^2)⁻¹ := by
        apply sum_le_sum
        intro r hr
        have hr' := mem_Ico.mp hr
        have hrN : r<N := lt_of_lt_of_le hr'.2 hm
        have hur : c*w j≤u r := (mul_le_mul_of_nonneg_left (hwmono j r hr'.1 hrN.le) hc.le).trans (hu r hrN.le).1
        have hur₁ : c*w j≤u (r+1) :=
          (mul_le_mul_of_nonneg_left (hwmono j (r+1) (by omega) (by omega)) hc.le).trans (hu (r+1) (by omega)).1
        have har := ha r hrN
        have hur0 : 0≤u r := (mul_pos hc hwj).le.trans hur
        have hden : A*c^2*(w j)^2≤a (r+1)*u r*u (r+1) := by
          convert mul_le_mul (mul_le_mul har hur (by positivity) (hA.le.trans har)) hur₁ (by positivity)
            (mul_nonneg (hA.le.trans har) hur0) using 1; ring
        simpa only [one_div] using one_div_le_one_div_of_le hbase hden
      _ = _ := by simp only [sum_const,nsmul_eq_mul,Nat.card_Ico]
  have hs0 : 0≤∑r∈Ico j m,(a (r+1)*u r*u (r+1))⁻¹ := by
    apply sum_nonneg
    intro r hr
    have hr' := mem_Ico.mp hr
    exact inv_nonneg.mpr (mul_nonneg (mul_nonneg (hA.le.trans (ha r (by omega)))
      ((mul_pos hc (hw r (by omega))).le.trans (hu r (by omega)).1))
      ((mul_pos hc (hw (r+1) (by omega))).le.trans (hu (r+1) (by omega)).1))
  have hprod := mul_le_mul (mul_le_mul (hu m hm).2 (hu j (hj.trans hm)).2 huj0 (mul_pos hC hwm).le)
    hs hs0 (by positivity : 0≤(C*w m)*(C*w j))
  have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hprod hwj.le) hwm.le
  calc
    _ ≤ _ := h
    _ = _ := by field_simp [hwm.ne',hwj.ne',hA.ne',hc.ne']

end
end jacobi.Finite
