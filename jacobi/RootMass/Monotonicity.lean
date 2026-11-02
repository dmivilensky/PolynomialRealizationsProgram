import jacobi.RootMass.Certificate

/-!
Article: jacobi, Theorem D.8.
The rational polynomial certificate gives positivity of the exact numerator
of Q' throughout the entire parameter half-line a>=-17/5. The endpoint
parameter is controlled by the printed positive matrices; increasing a adds
an explicit polynomial with nonnegative coefficients.
Source: the supplement's polynomial expansion, proved by exact ring identities.
Use: positivity of this polynomial is the only nontrivial scalar sign in strict constraint monotonicity.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The exact translated numerator of the logarithmic Q derivative.
Use: positivity of this polynomial is the only nontrivial scalar sign in strict constraint monotonicity.
Article: jacobi, Theorem D.8.
-/
def N (a t : ℝ) : ℝ := 12*t^6+4*(5*a+18)*t^5+2*(3*a^2+50*a+120)*t^4+
  8*(a+6)*(3*a+10)*t^3+34*(a+4)^2*t^2+20*(a+4)^2*t+4*(a+4)^2

/-- The translated numerator differs from its sharp endpoint by two manifestly nonnegative polynomials.
Use: extends the exact endpoint matrix certificate to every larger permitted eta.
Article: jacobi, Theorem D.8.
Proof: expand in h=a+17/5 and compare the literal polynomial coefficients. -/
theorem N_shift (a t : ℝ) : N a t=PiSharp t/25+
    (a+17/5)*(20*t^5+(296/5:ℝ)*t^4+(304/5:ℝ)*t^3+(204/5:ℝ)*t^2+24*t+24/5)+
    (a+17/5)^2*(6*t^4+24*t^3+34*t^2+20*t+4) := by
  unfold N PiSharp
  ring

/-- The exact translated derivative numerator is strictly positive on the entire parameter and spatial half-lines.
Use: proves Q'>0 globally, including the endpoint eta=-34/5.
Article: jacobi, Theorem D.8.
Proof: the actual matrix certificate makes the endpoint term strictly positive;
the two exact correction polynomials are nonnegative. -/
theorem N_pos {a t : ℝ} (ha : -(17/5:ℝ)≤a) (ht : 0≤t) : 0<N a t := by
  have hp := PiSharp_pos ht
  have hh : 0≤a+17/5 := by linarith
  rw [N_shift]
  positivity

/-- The complete theorem parameter range lies strictly inside the smooth profile range.
Use: every inverse-coordinate and positive-denominator theorem applies at the sharp endpoint too.
Article: jacobi, Theorem D.8.
Proof: (17/5)²<12 and the square root is nonnegative. -/
theorem sharp_parameter {a : ℝ} (ha : -(17/5:ℝ)≤a) : -2*sqrt 3<a := by
  have hs := sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hp := sqrt_nonneg (3:ℝ)
  nlinarith

/-- The rational function controlling the root-mass moment quadrature.
Use: rewriting the mass-defining constraint with Q makes strict monotonicity pointwise.
Article: jacobi, Theorem D.8.
-/
def Q (a n : ℝ) : ℝ := n^4*(n^2-1)^2/(p a n*q a n)

/-- The exact positive-factor expression for the derivative of Q.
Use: the matrix certificate and the inverse-coordinate derivative imply the strict derivative of the defining constraint.
Article: jacobi, Theorem D.8.
-/
def QSlope (a n : ℝ) : ℝ := n^3*(n^2-1)*N a (n-1)/(p a n*q a n)^2

/-- The controlling rational function has its exact literal derivative.
Use: supplies an actual derivative identity before any monotonicity or differentiation under the quadrature integral.
Article: jacobi, Theorem D.8.
Proof: differentiate numerator and denominator, clear the genuinely nonzero
polynomial denominator, and verify the translated degree-six numerator exactly. -/
theorem Q_hasDerivAt {a n : ℝ} (hp : p a n≠0) (hq : q a n≠0) : HasDerivAt (Q a) (QSlope a n) n := by
  -- This checks the full translated polynomial identity, including its sharp-parameter coefficients.
  have hP : HasDerivAt (p a) (6*n+a) n := by
    convert (((hasDerivAt_id n).pow 2).const_mul 3).add ((hasDerivAt_id n).const_mul a) |>.add_const 1 using 1
    · rfl
    · norm_num; ring
  have hQ : HasDerivAt (q a) (2*n+a) n := by
    convert ((hasDerivAt_id n).pow 2).add ((hasDerivAt_id n).const_mul a) |>.add_const 3 using 1
    · rfl
    · norm_num
  convert (((hasDerivAt_id n).pow 4).mul ((((hasDerivAt_id n).pow 2).sub_const 1).pow 2)).div
    (hP.mul hQ) (mul_ne_zero hp hq) using 1
  · rfl
  · dsimp only [QSlope,Pi.pow_apply,Pi.mul_apply,id_eq]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one]
    field_simp [hp,hq]
    unfold p q N
    ring

/-- The actual Q derivative is strictly positive at every n>1 in the full sharp theorem range.
Use: strict increase of the defining quadrature follows from its actual increasing inverse-coordinate arguments.
Article: jacobi, Theorem D.8.
Proof: all denominator factors are positive, and the certified translated numerator is strictly positive. -/
theorem QSlope_pos {a n : ℝ} (ha : -(17/5:ℝ)≤a) (hn : 1<n) : 0<QSlope a n := by
  have hpa := sharp_parameter ha
  have hp := (p_bounds hpa hn.le).1.trans_le (p_bounds hpa hn.le).2.1
  have hq := q_pos hpa hn.le
  have hN := N_pos ha (sub_nonneg.mpr hn.le)
  have hn0 : 0<n := zero_lt_one.trans hn
  have hn2 : 0<n^2-1 := by nlinarith
  exact div_pos (mul_pos (mul_pos (pow_pos hn0 3) hn2) hN) (sq_pos_of_pos (mul_pos hp hq))

/-- The actual rational Q is strictly increasing on its full closed profile domain.
Use: yields strict monotonicity of the original nonsingular constraint integral by actual pointwise comparison.
Article: jacobi, Theorem D.8.
Proof: the rational derivative exists also at one, while its proved strict
sign holds in the open interior; apply the actual mean value theorem. -/
theorem Q_strictMono {a : ℝ} (ha : -(17/5:ℝ)≤a) : StrictMonoOn (Q a) (Ici (1:ℝ)) := by
  -- The zero derivative at n=1 causes no gap in strict monotonicity of the closed-domain function.
  have hd (n : ℝ) (hn : 1≤n) := Q_hasDerivAt
    ((p_bounds (sharp_parameter ha) hn).1.trans_le (p_bounds (sharp_parameter ha) hn).2.1).ne'
    (q_pos (sharp_parameter ha) hn).ne'
  apply strictMonoOn_of_deriv_pos (convex_Ici 1)
  · exact fun n hn => (hd n hn).continuousAt.continuousWithinAt
  · intro n hn
    rw [interior_Ici] at hn
    rw [(hd n (mem_Ioi.mp hn).le).deriv]
    exact QSlope_pos ha hn

end
end jacobi.RootMass
