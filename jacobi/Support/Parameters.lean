import jacobi.Reference.Parameters
import jacobi.Jacobi.ZeroModel

/-!
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
The actual support chain uses the same gamma exponents and finite frequency
as the already formalized two-edge node model. The original step satisfies
N*h=pi exactly. Parameter exchange and the Darboux shift preserve this step.
Use: coefficientA and coefficientC are the literal original support coefficients.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology

/-- The original average of the two genuine endpoint exponents.
Use: coefficientA and coefficientC are the literal original support coefficients.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
-/
def averageGamma (a b : ℝ) : ℝ := (gamma a+gamma b)/2

/-- The original angular lattice step of the actual finite support chain.
Use: the support coefficients, nodes and exact Darboux spectral deletion all use this same physical step.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
-/
def step (a b : ℝ) (n : ℕ) : ℝ := Real.pi/ jacobi.Jacobi.frequency a b n

/-- The earlier actual Jacobi frequency is precisely the support chain's printed gamma frequency.
Use: coefficient bounds and exact boundary sine cancellations retain the same original N as the already proved Jacobi node estimates.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
Proof: expand the original affine parameter definitions. -/
theorem frequency_gamma (a b : ℝ) (n : ℕ) :
    jacobi.Jacobi.frequency a b n=(n:ℝ)-1+gamma a+gamma b := by
  unfold jacobi.Jacobi.frequency gamma
  ring

/-- Both actual endpoint exponents and their genuine average are positive throughout the original parameter range.
Use: all support sine arguments are strictly between zero and the actual period.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
Proof: the already proved gamma lower bounds imply all three strict positive bounds. -/
theorem parameter_pos {a b : ℝ} (ha : -1<a) (hb : -1<b) :
    0<gamma a ∧ 0<gamma b ∧ 0<averageGamma a b := by
  have hA := (parameters ha).1
  have hB := (parameters hb).1
  dsimp [averageGamma]
  exact ⟨by linarith,by linarith,by linarith⟩

/-- The genuine original support lattice step is positive at every nonempty finite dimension.
Use: the support sine arguments retain the original positive orientation.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
Proof: the already proved actual finite Jacobi frequency is strictly positive. -/
theorem step_pos {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (hn : 0<n) :
    0<step a b n := div_pos Real.pi_pos (jacobi.Jacobi.frequency_pos ha hb hn)

/-- The actual finite support period is exactly pi.
Use: support coefficient reflection and every terminal coefficient cancellation use the unchanged original truncation identity.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
Proof: cancel the genuine positive original frequency in the literal step. -/
theorem frequency_mul_step {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (hn : 0<n) :
    jacobi.Jacobi.frequency a b n*step a b n=Real.pi := by
  rw [step,mul_div_cancel₀ _ (jacobi.Jacobi.frequency_pos ha hb hn).ne']

/-- Every genuine coordinate strictly within the original finite period has positive sine.
Use: coefficientA_pos and coefficientC_pos discharge all numerator and denominator signs for the original chain.
Article: jacobi, Appendix C.3 (askey–Wilson comparison chain).
Source: positivity of sine on the physical half period.
Proof: multiplication by the actual positive step sends (0,N) into (0,pi), by its proved exact period identity. -/
theorem sin_position_pos {a b x : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (hn : 0<n)
    (hx : 0<x) (hN : x< jacobi.Jacobi.frequency a b n) : 0<sin (x*step a b n) := by
  apply Real.sin_pos_of_pos_of_lt_pi (mul_pos hx (step_pos ha hb hn))
  rw [← frequency_mul_step ha hb hn]
  exact mul_lt_mul_of_pos_right hN (step_pos ha hb hn)

/-- Exchanging the two original endpoint indices preserves the actual support step.
Use: the original support reflection identifies the opposite-edge coefficients and weights.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the literal original frequency is symmetric in its two parameters. -/
theorem step_swap (a b : ℝ) (n : ℕ) : step b a n=step a b n := by
  unfold step jacobi.Jacobi.frequency
  congr 2
  ring

/-- Deleting the original upper node and shifting its endpoint parameter preserves the actual lattice step.
Use: the support Darboux factorization determines the entire actual finite spectrum inductively.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Source: endpoint Christoffel/Darboux transformation for finite Jacobi matrices.
Proof: the degree decreases by one and gamma_alpha increases by one, so the original frequency is unchanged. -/
theorem step_darboux (a b : ℝ) (n : ℕ) : step (a+2) b n=step a b (n+1) := by
  unfold step jacobi.Jacobi.frequency
  congr 1
  push_cast
  ring

end
end jacobi.Support
