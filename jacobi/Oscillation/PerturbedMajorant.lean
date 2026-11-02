import jacobi.Oscillation.PerturbedInvariantBound

/-!
Article: jacobi, Proposition B.1.
The actual linear phase bound turns the exact fourth-order Lipschitz
remainder into an integrable inverse-square bound. The remaining e,e'
terms have size epsilon/N, without a logarithmic loss on growing intervals.
Use: integrates the averaged actual finite Jacobi phase correction over the full interval of length O(N), proving the quantitative input to Proposition B.1 (a).
-/
namespace jacobi.Oscillation
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- Actual linear phase stability and literal small C1 potential bounds give a uniform integrable majorant for the genuine corrected derivative difference.
Use: integrates the averaged actual finite Jacobi phase correction over the full interval of length O(N), proving the quantitative input to Proposition B.1 (a).
Article: jacobi, Proposition B.1.
Proof: the fourth-order Lipschitz term gains the actual bound B*epsilon*x,
so it is at most a fixed multiple of epsilon/x^3, hence epsilon/x^2.
Bound the two mixed terms by epsilon/x^2 and the quadratic and derivative
terms by epsilon/N. A single explicit positive coefficient dominates all terms. -/
theorem perturbedInvariant_majorant (c : ℝ) (f g e e' : ℝ → ℝ) {x N epsilon B : ℝ}
    (hx : 1≤x) (hN : 0<N) (heps : 0<epsilon) (hB : 0≤B)
    (hepsN : epsilon≤1/N) (hdelta : |f x-g x|≤B*epsilon*x)
    (he : |e x|≤epsilon) (he' : |e' x|≤epsilon/N) :
    |perturbedInvariantSlope c f e e' x-phaseInvariantSlope c g x|≤
      ((4*c^2+2*|c|)*B+2*|c|+1)*epsilon*(1/x^2+1/N) := by
  -- Linear phase control preserves an integrable power of the actual argument, which is the decisive uniformity improvement over an unaveraged absolute perturbation bound.
  have hxp : 0<x := by linarith
  let A := 4*c^2+2*|c|
  let K := A*B+2*|c|+1
  have hA : 0≤A := by dsimp [A]; positivity
  have hK : 1≤K := by dsimp [K]; nlinarith [mul_nonneg hA hB,abs_nonneg c]
  have hfirst : A*|f x-g x|/x^4≤A*B*epsilon/x^2 := by
    calc
      _ ≤ A*(B*epsilon*x)/x^4 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdelta hA) (by positivity)
      _ = A*B*epsilon/x^3 := by field_simp [hxp.ne']
      _ ≤ A*B*epsilon/x^2 := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by nlinarith [mul_le_mul_of_nonneg_left hx (show 0≤x^2 by positivity)])
  have hsecond : 2*|c| *|e x|/x^2≤2*|c| *epsilon/x^2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) (by positivity)
  have hs : (e x)^2≤epsilon^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg (e x)) heps.le).mpr he
    simpa only [sq_abs] using hh
  have hthird : (e x)^2/2≤epsilon/(2*N) := by
    have hm := mul_le_mul_of_nonneg_left hepsN heps.le
    have heq : epsilon*(1/N)/2=epsilon/(2*N) := by ring
    rw [← heq]
    exact div_le_div_of_nonneg_right (hs.trans (by nlinarith)) (by norm_num)
  have hfourth : |e' x|/4≤epsilon/(4*N) := by
    have hh := div_le_div_of_nonneg_right he' (show (0:ℝ)≤4 by norm_num)
    convert hh using 1
    ring
  have hmain := perturbedInvariantSlope_remainder c f g e e' hx
  have hrem : A*B*epsilon/x^2+2*|c| *epsilon/x^2+epsilon/(2*N)+epsilon/(4*N)≤K*epsilon*(1/x^2+1/N) := by
    have heq : K*epsilon*(1/x^2+1/N)-
        (A*B*epsilon/x^2+2*|c| *epsilon/x^2+epsilon/(2*N)+epsilon/(4*N))=
        epsilon/x^2+(K-3/4)*epsilon/N := by dsimp [K]; ring
    have hK0 : 0≤K-3/4 := by linarith
    have hp : 0≤epsilon/x^2+(K-3/4)*epsilon/N := by positivity
    linarith
  exact hmain.trans ((add_le_add (add_le_add (add_le_add hfirst hsecond) hthird) hfourth).trans hrem)

end
end jacobi.Oscillation
