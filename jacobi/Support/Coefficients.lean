import jacobi.Support.Parameters

/-!
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
The original trigonometric A_m,C_m coefficients have positive interior
numerators and denominators and the exact terminal zeros. The formulas
are defined literally even at a zero terminal denominator: the proved
terminal numerator zero makes their value the required zero.
Use: naturalChain uses A_(m-1)*C_m/4 as its genuine squared coupling; the Darboux factorization deletes the actual top node.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The literal original upper birth coefficient of the finite support chain.
Use: naturalChain uses A_(m-1)*C_m/4 as its genuine squared coupling; the Darboux factorization deletes the actual top node.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
-/
def coefficientA (a b : ℝ) (n m : ℕ) : ℝ :=
  sin (((m:ℝ)+gamma a+1/2)*step a b n)*sin (((m:ℝ)+2*averageGamma a b)*step a b n)/
    (sin (((m:ℝ)+averageGamma a b)*step a b n)*sin (((m:ℝ)+averageGamma a b+1/2)*step a b n))

/-- The literal original lower birth coefficient of the finite support chain.
Use: the same C_m enters the actual symmetric coupling and the original top-node product solution.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
-/
def coefficientC (a b : ℝ) (n m : ℕ) : ℝ :=
  sin ((m:ℝ)*step a b n)*sin (((m:ℝ)+gamma b-1/2)*step a b n)/
    (sin (((m:ℝ)+averageGamma a b-1/2)*step a b n)*sin (((m:ℝ)+averageGamma a b)*step a b n))

/-- The actual support upper coefficient is strictly positive at every original nonterminal row.
Use: naturalChain_irreducible and the original positive top-node solution require these actual coefficient signs.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
Proof: all four literal sine coordinates lie strictly between zero and the actual original period N; their genuine positive sine factors give the quotient sign. -/
theorem coefficientA_pos {a b : ℝ} (ha : -1<a) (hb : -1<b) {n m : ℕ} (hm : m+1<n) :
    0<coefficientA a b n m := by
  -- Use the exact original finite period for each shifted sine; no asymptotic degree restriction is needed.
  have hg := parameter_pos ha hb
  have hmr : (m:ℝ)+2≤(n:ℝ) := by exact_mod_cast (show m+2≤n by omega)
  have hm0 : (0:ℝ)≤m := Nat.cast_nonneg m
  have hn : 0<n := by omega
  have hfreq := frequency_gamma a b n
  unfold coefficientA
  apply div_pos <;> apply mul_pos <;> apply sin_position_pos ha hb hn
  all_goals dsimp [averageGamma] at *; linarith [hg.1,hg.2.1,hfreq]

/-- The actual support lower coefficient is strictly positive at every original noninitial row.
Use: the actual support matrix is irreducible throughout the full original parameter range.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
Proof: all original sine coordinates are strictly between zero and N. The potentially negative shift gamma_beta-1/2 is compensated by the genuine index m>=1. -/
theorem coefficientC_pos {a b : ℝ} (ha : -1<a) (hb : -1<b) {n m : ℕ}
    (hm : 0<m) (hmn : m<n) : 0<coefficientC a b n m := by
  -- The actual positive row index fixes both shifted lower-coordinate signs uniformly in the original parameters.
  have hg := parameter_pos ha hb
  have hmr : (m:ℝ)+1≤n := by exact_mod_cast (show m+1≤n by omega)
  have hm1 : (1:ℝ)≤m := by exact_mod_cast hm
  have hn : 0<n := by omega
  have hfreq := frequency_gamma a b n
  unfold coefficientC
  apply div_pos <;> apply mul_pos <;> apply sin_position_pos ha hb hn
  all_goals dsimp [averageGamma] at *; linarith [hg.1,hg.2.1,hfreq]

/-- The actual incoming original support coefficient is identically zero, including the exceptional average parameter.
Use: naturalChain fixes its unused incoming coupling and the top-node recurrence starts with the original constant one.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
Proof: the literal numerator contains sin(0), so its quotient is zero even when a totalized terminal denominator is zero. -/
theorem coefficientC_zero (a b : ℝ) (n : ℕ) : coefficientC a b n 0=0 := by
  simp only [coefficientC,Nat.cast_zero,zero_mul,Real.sin_zero,zero_div]

/-- The actual original support upper coefficient vanishes at the genuine last row in every nonempty dimension.
Use: the finite chain closes exactly and the rectangular Darboux deletion retains precisely one original top eigenvalue.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
Proof: its original second numerator angle is exactly N*h=pi. Sine vanishes there independently of any denominator, covering the exceptional average parameter without a density argument. -/
theorem coefficientA_terminal {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (hn : 0<n) :
    coefficientA a b n (n-1)=0 := by
  have harg : ((n-1:ℕ):ℝ)+2*averageGamma a b= jacobi.Jacobi.frequency a b n := by
    rw [Nat.cast_sub hn,frequency_gamma]
    dsimp [averageGamma]
    push_cast
    ring
  simp only [coefficientA,harg,frequency_mul_step ha hb hn,Real.sin_pi,mul_zero,zero_div]

end
end jacobi.Support
