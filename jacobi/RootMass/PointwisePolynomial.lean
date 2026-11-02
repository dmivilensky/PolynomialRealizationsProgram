import jacobi.RootMass.Polynomials

/-!
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
The literal cubic h(n)=n³-c*n²+b²*n is minimized globally on n>=0.
Below the cutoff its unique minimizer is zero. Above it the unique minimizer
is the printed larger root, strictly above b. At the boundary both zero
and b attain the minimum; this is the genuine jump of the compact profile.
Source: exact factorization of the cubic difference at its larger stationary point.
Use: its global minimizers determine the density even though the root term is nonconvex in m.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The actual scalar polynomial in the root-mass pointwise minimum principle.
Use: its global minimizers determine the density even though the root term is nonconvex in m.
Article: jacobi, Appendix D.5 (compact root-mass profile).
-/
def h (b c n : ℝ) : ℝ := n^3-c*n^2+b^2*n

/-- The larger positive stationary root of the scalar inner polynomial.
Use: gives the actual normalized compact profile inside its free boundary.
Article: jacobi, Appendix D.5 (compact root-mass profile).
-/
def upperRoot (b c : ℝ) : ℝ := (c+sqrt (c^2-3*b^2))/3

/-- Below the true switching coefficient, the scalar polynomial is strictly positive at every positive argument.
Use: the pointwise minimizer must vanish in the exterior of the optimizing compact profile.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: h(n)=n*((n-b)²+(2*b-c)*n), whose last term is strictly positive. -/
theorem h_pos_below {b c n : ℝ} (hc : c<2*b) (hn : 0<n) : 0<h b c n := by
  have hh := mul_pos hn (add_pos_of_nonneg_of_pos (sq_nonneg (n-b)) (mul_pos (sub_pos.mpr hc) hn))
  convert hh using 1
  unfold h
  ring

/-- At the true switching coefficient, precisely zero and b attain the scalar minimum.
Use: explains the one-sided profile value b at the free boundary and the permissible null-set choice there.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: factor the literal polynomial and use nonnegativity of n. -/
theorem h_switch {b n : ℝ} (hn : 0≤n) :
    0≤h b (2*b) n ∧ (h b (2*b) n=0 ↔ n=0 ∨ n=b) := by
  have hh : h b (2*b) n=n*(n-b)^2 := by unfold h; ring
  rw [hh]
  exact ⟨mul_nonneg hn (sq_nonneg _),by simp only [mul_eq_zero,pow_eq_zero_iff (by decide : 2≠0),sub_eq_zero]⟩

/-- Above the switching coefficient the printed larger root is above b and satisfies the true stationary equation.
Use: selects the exact positive density branch, excluding the smaller local maximum.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: the radicand is positive. Its positive square root exceeds 3*b-c
when needed, and its exact square verifies the stationary identity. -/
theorem upperRoot_properties {b c : ℝ} (hb : 0<b) (hc : 2*b<c) :
    b<upperRoot b c ∧ 3*(upperRoot b c)^2-2*c*upperRoot b c+b^2=0 ∧ 0<2*upperRoot b c-c := by
  -- The same positive square-root branch supplies both normalization and strict global-minimum sign.
  have hD : 0<c^2-3*b^2 := by nlinarith
  have hs := sq_sqrt hD.le
  have hsp := sqrt_pos.mpr hD
  have hr : b<upperRoot b c := by unfold upperRoot; nlinarith
  have he : 3*(upperRoot b c)^2-2*c*upperRoot b c+b^2=0 := by
    unfold upperRoot
    nlinarith
  have hcoef : 0<2*upperRoot b c-c := by unfold upperRoot; nlinarith
  exact ⟨hr,he,hcoef⟩

/-- The printed larger root is the unique global minimum of the actual scalar polynomial above the cutoff.
Use: turns the genuine variational pointwise principle into the unique compact density formula.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: at the larger stationary root r, h(n)-h(r)=(n-r)²*(n+2*r-c).
The second factor is strictly positive for every n>=0, so equality forces n=r. -/
theorem upperRoot_minimizes {b c : ℝ} (hb : 0<b) (hc : 2*b<c) {n : ℝ} (hn : 0≤n) :
    h b c (upperRoot b c)≤h b c n ∧
      (h b c (upperRoot b c)=h b c n ↔ n=upperRoot b c) := by
  -- Factor the global objective difference, rather than checking only the Euler derivative.
  obtain ⟨_hr,he,hcoef⟩ := upperRoot_properties hb hc
  have hid : h b c n-h b c (upperRoot b c)=(n-upperRoot b c)^2*(n+2*upperRoot b c-c) := by
    unfold h
    nlinarith [congrArg (fun z : ℝ => (n-upperRoot b c)*z) he]
  have hp : 0<n+2*upperRoot b c-c := by linarith
  constructor
  · have hh := mul_nonneg (sq_nonneg (n-upperRoot b c)) hp.le
    linarith
  · constructor
    · intro hh
      have hz : (n-upperRoot b c)^2=0 := (mul_eq_zero.mp (by linarith :
        (n-upperRoot b c)^2*(n+2*upperRoot b c-c)=0)).resolve_right hp.ne'
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)
    · intro hh
      rw [hh]

end
end jacobi.RootMass
