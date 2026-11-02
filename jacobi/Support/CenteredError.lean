import jacobi.Support.CouplingIdentity

/-!
Article: jacobi, Appendix C.3 (coefficient bounds).
An elementary quantitative estimate for the exact centered coupling
quotient. The support specialization supplies the actual positive
denominator bounds and genuine sine-square estimates.
Use: coupling_error supplies all these scalar bounds from the actual original support sines, proving the printed coefficient perturbation estimate.
-/
namespace jacobi.Support
noncomputable section
open Real

/-- The exact centered squared-coupling quotient differs from one by a uniform inverse-square index bound under its genuine positive denominator estimates.
Use: coupling_error supplies all these scalar bounds from the actual original support sines, proving the printed coefficient perturbation estimate.
Article: jacobi, Appendix C.3 (coefficient bounds).
Proof: split the exact difference into (T^2-P^2-Q^2)/(S^2-T^2) and the positive fourth-order term P^2*Q^2/(S^2*(S^2-T^2)). The actual lower denominator bounds cancel the original step powers; m>=1 bounds the remaining inverse fourth power by its inverse square. -/
theorem centered_quotient_error {S P Q T h m c d A B C : ℝ}
    (hm:1≤m) (hh:0<h) (hc:0<c) (hd:0<d) (hS:c*m*h≤S)
    (hD:d*m^2*h^2≤S^2-T^2) (hA:0≤A) (hB:0≤B) (hC:0≤C)
    (hP:P^2≤A*h^2) (hQ:Q^2≤B*h^2) (hT:T^2≤C*h^2) :
    |((S^2-P^2)*(S^2-Q^2))/(S^2*(S^2-T^2))-1|≤
      ((A+B+C)/d+A*B/(c^2*d))/m^2 := by
  -- The fourth-order term is retained exactly; it is not discarded by a formal big-O cancellation.
  have hm0 : 0<m := by linarith
  have hs : 0<S := lt_of_lt_of_le (by positivity) hS
  have hd0 : 0<S^2-T^2 := lt_of_lt_of_le (by positivity) hD
  have he : ((S^2-P^2)*(S^2-Q^2))/(S^2*(S^2-T^2))-1=
      (T^2-P^2-Q^2)/(S^2-T^2)+(P^2*Q^2)/(S^2*(S^2-T^2)) := by
    field_simp [hs.ne',hd0.ne']
    ring
  have hnum : |T^2-P^2-Q^2|≤(A+B+C)*h^2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg P,sq_nonneg Q,sq_nonneg T]
  have hprod : P^2*Q^2≤A*B*h^4 := by
    convert mul_le_mul hP hQ (sq_nonneg _) (mul_nonneg hA (sq_nonneg h)) using 1; ring
  have hs2 : (c*m*h)^2≤S^2 := sq_le_sq₀ (by positivity) hs.le |>.mpr hS
  have hden : c^2*d*m^4*h^4≤S^2*(S^2-T^2) := by
    convert mul_le_mul hs2 hD (by positivity) (sq_nonneg S) using 1; ring
  have hfirst : |(T^2-P^2-Q^2)/(S^2-T^2)|≤((A+B+C)/d)/m^2 := by
    rw [abs_div,abs_of_pos hd0]
    calc
      _ ≤ ((A+B+C)*h^2)/(d*m^2*h^2) := div_le_div₀ (by positivity) hnum (by positivity) hD
      _ = _ := by field_simp [hd.ne',hm0.ne',hh.ne']
  have hsecond : |(P^2*Q^2)/(S^2*(S^2-T^2))|≤(A*B/(c^2*d))/m^2 := by
    rw [abs_div,abs_of_pos (mul_pos (sq_pos_of_pos hs) hd0),abs_of_nonneg (mul_nonneg (sq_nonneg P) (sq_nonneg Q))]
    calc
      _ ≤ (A*B*h^4)/(c^2*d*m^4*h^4) := div_le_div₀ (by positivity) hprod (by positivity) hden
      _ = (A*B/(c^2*d))/m^4 := by field_simp [hc.ne',hd.ne',hm0.ne',hh.ne']
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hm0) (by nlinarith [sq_nonneg (m^2-1)])
  rw [he]
  calc
    _ ≤ |(T^2-P^2-Q^2)/(S^2-T^2)|+|(P^2*Q^2)/(S^2*(S^2-T^2))| := abs_add_le _ _
    _ ≤ ((A+B+C)/d)/m^2+(A*B/(c^2*d))/m^2 := add_le_add hfirst hsecond
    _ = _ := by ring

end
end jacobi.Support
