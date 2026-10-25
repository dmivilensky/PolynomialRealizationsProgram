import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.Ring

/-! A quintic with two genuine double contacts has the exact source factor.+The argument uses divisibility and degree; no interval containing zero stands
in for a contact equation. -/
noncomputable section
namespace polyak.CertifiedExamples.Exact313.Factor
open Polynomial

theorem square_dvd_of_double_root (p : ℝ[X]) (u : ℝ)
    (h : p.eval u=0) (hd : p.derivative.eval u=0) : (X-C u)^2 ∣ p := by
  obtain ⟨s,hs⟩ := (dvd_iff_isRoot.mpr h : X-C u ∣ p)
  have hs0 : s.eval u=0 := by
    rw [hs] at hd
    simpa using hd
  obtain ⟨t,ht⟩ := (dvd_iff_isRoot.mpr hs0 : X-C u ∣ s)
  refine ⟨t,?_⟩
  rw [hs,ht]
  ring

theorem cubic_eq_zero_of_double_roots (p : ℝ[X]) {u v : ℝ} (huv : u≠v)
    (hp : p.natDegree≤3) (hu : p.eval u=0) (hv : p.eval v=0)
    (hdu : p.derivative.eval u=0) (hdv : p.derivative.eval v=0) : p=0 := by
  have hc : IsCoprime (X-C u : ℝ[X]) (X-C v) :=
    isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr huv).isUnit
  have hc2 : IsCoprime ((X-C u : ℝ[X])^2) ((X-C v)^2) := hc.pow
  have hdvd := hc2.mul_dvd (square_dvd_of_double_root p u hu hdu)
    (square_dvd_of_double_root p v hv hdv)
  apply eq_zero_of_dvd_of_natDegree_lt hdvd
  have hdeg : (((X-C u : ℝ[X])^2)*((X-C v)^2)).natDegree=4 := by
    compute_degree!
  rw [hdeg]
  omega

def quintic (r a b d c : ℝ) : ℝ :=
  (d+b*c+a*c^2)*(1+8*r*c^2*(1+c))+(1+c)*(4*r*c*(2*c^2-1)-1)

theorem quintic_factor (r a b d u v : ℝ) (huv : u≠v)
    (hu : quintic r a b d u=0) (hv : quintic r a b d v=0)
    (hdu : deriv (quintic r a b d) u=0) (hdv : deriv (quintic r a b d) v=0)
    (c : ℝ) :
    quintic r a b d c=(c-u)^2*(c-v)^2*
      (8*r*a*c+8*r*(b+a+1+2*a*(u+v))) := by
  let S := u+v
  let P := u*v
  let A := 8*r*a
  let B := 8*r*(b+a+1+2*a*S)
  let N : ℝ[X] := (C d+C b*X+C a*X^2)*(1+C (8*r)*X^2*(1+X))+
    (1+X)*(C (4*r)*X*(2*X^2-1)-1)
  let Q : ℝ[X] := (X-C u)^2*(X-C v)^2*(C A*X+C B)
  have hN (x : ℝ) : N.eval x=quintic r a b d x := by
    simp [N,quintic]
  have hQ (x : ℝ) : Q.eval x=(x-u)^2*(x-v)^2*(A*x+B) := by
    simp [Q]
  have hR : N-Q=
      C (8*b*r+8*d*r+8*r-A*(S^2+2*P)+2*B*S)*X^3+
      C (a+8*d*r-4*r+2*A*S*P-B*(S^2+2*P))*X^2+
      C (b-4*r-1-A*P^2+2*B*S*P)*X+C (d-1-B*P^2) := by
    dsimp [N,Q,A,B,S,P]
    simp only [map_add,map_sub,map_mul,map_pow,map_ofNat,map_one]
    ring
  have hp : (N-Q).natDegree≤3 := by
    rw [hR]
    exact natDegree_cubic_le
  have hNu : N.derivative.eval u=0 := by
    rw [← N.deriv]
    simpa only [hN] using hdu
  have hNv : N.derivative.eval v=0 := by
    rw [← N.deriv]
    simpa only [hN] using hdv
  have hQdu : Q.derivative.eval u=0 := by simp [Q,derivative_mul,derivative_pow]
  have hQdv : Q.derivative.eval v=0 := by simp [Q,derivative_mul,derivative_pow]
  have hz : N-Q=0 := cubic_eq_zero_of_double_roots (N-Q) huv hp
    (by simp [hN,hQ,hu]) (by simp [hN,hQ,hv])
    (by simp [hNu,hQdu]) (by simp [hNv,hQdv])
  have he := congrArg (fun p : ℝ[X]=>p.eval c) (sub_eq_zero.mp hz)
  simpa [hN,hQ,A,B,S] using he

end polyak.CertifiedExamples.Exact313.Factor
