import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(c), actual Gaussian nodes in the original measure support.
Use: isolate a true positive Gaussian weight by its spectral cardinal polynomial and derive the genuine node window from original integral positivity.
Source: the classical Gaussian cardinal-polynomial support argument, with the full polynomial degree bound proved here.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Polynomial
open scoped BigOperators
variable {N : ℕ}

/-- The genuine spectral cardinal polynomial vanishing at every other actual quadrature node.
Use: The genuine spectral cardinal polynomial vanishing at every other actual quadrature node.
Article: main_krylov, prop:phi(c), actual Gaussian nodes in the original measure support.
Proof: Multiply the original linear factors at all indices except the chosen site. -/
def spectralCardinalPolynomial (lam : Fin N → ℝ) (j : Fin N) : ℝ[X] :=
  ∏ k∈Finset.univ.erase j,(X-C (lam k))

/-- The actual spectral cardinal polynomial has degree the quadrature size minus one.
Use: The actual spectral cardinal polynomial has degree the quadrature size minus one.
Article: main_krylov, prop:phi(c), actual Gaussian nodes in the original measure support.
Proof: Use monicity of every original factor and the cardinality of the erased index set. -/
theorem spectralCardinal_degree (lam : Fin N → ℝ) (j : Fin N) :
    (spectralCardinalPolynomial lam j).natDegree=N-1 := by
  rw [spectralCardinalPolynomial,natDegree_prod_of_monic (f := fun k => X-C (lam k)) (Finset.univ.erase j) (fun k _ => monic_X_sub_C (lam k))]
  simp

/-- Each different true quadrature node annihilates the genuine spectral cardinal polynomial.
Use: Each different true quadrature node annihilates the genuine spectral cardinal polynomial.
Article: main_krylov, prop:phi(c), actual Gaussian nodes in the original measure support.
Proof: The corresponding original linear factor vanishes in the finite product. -/
theorem spectralCardinal_other (lam : Fin N → ℝ) (j k : Fin N) (hkj : k≠j) :
    (spectralCardinalPolynomial lam j).eval (lam k)=0 := by
  rw [spectralCardinalPolynomial,eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hkj,Finset.mem_univ k⟩) (by simp)

/-- Distinct genuine quadrature nodes give a nonzero cardinal polynomial value at its own node.
Use: Distinct genuine quadrature nodes give a nonzero cardinal polynomial value at its own node.
Article: main_krylov, prop:phi(c), actual Gaussian nodes in the original measure support.
Proof: Every remaining original linear factor is nonzero by true spectral injectivity. -/
theorem spectralCardinal_self_ne_zero (lam : Fin N → ℝ) (hinj : Function.Injective lam) (j : Fin N) :
    (spectralCardinalPolynomial lam j).eval (lam j)≠0 := by
  rw [spectralCardinalPolynomial,eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  simp only [eval_sub,eval_X,eval_C]
  exact sub_ne_zero.mpr (fun he => (Finset.mem_erase.mp hk).1 (hinj he).symm)

/-- Exact Gaussian quadrature and positive genuine weights transfer each linear localizing square inequality to every actual node.
Use: Exact Gaussian quadrature and positive genuine weights transfer each linear localizing square inequality to every actual node.
Article: main_krylov, prop:phi(c), actual Gaussian nodes in the original measure support.
Proof: The cardinal square isolates one positive coefficient in the actual exact polynomial sum; its degree lies below twice the rule size. -/
theorem finite_gauss_nonnegative_node (lam w : Fin N → ℝ) (hinj : Function.Injective lam)
    (hw : ∀ j,0 < w j) (L : ℝ[X] →ₗ[ℝ] ℝ)
    (hGauss : ∀ p : ℝ[X],p.natDegree<2*N → (∑ j,w j*p.eval (lam j))=L p)
    (r : ℝ[X]) (hr : r.natDegree≤1) (hpos : ∀ q : ℝ[X],0≤L (r*q^2)) (j : Fin N) :
    0≤r.eval (lam j) := by
  -- The actual cardinal square isolates one original positive weight within the genuine Gaussian degree bound.
  let q := spectralCardinalPolynomial lam j
  have hqdeg : q.natDegree=N-1 := spectralCardinal_degree lam j
  have hp : (r*q^2).natDegree<2*N := by
    have hmul : (r*q^2).natDegree≤r.natDegree+(q^2).natDegree := natDegree_mul_le
    have hpow : (q^2).natDegree≤2*q.natDegree := natDegree_pow_le
    have hN := j.isLt
    omega
  have h := hpos q
  rw [← hGauss (r*q^2) hp] at h
  have hsum : (∑ k,w k*(r*q^2).eval (lam k))=w j*r.eval (lam j)*(q.eval (lam j))^2 := by
    rw [Finset.sum_eq_single j]
    · simp only [eval_mul,eval_pow]
      ring
    · intro k _ hkj
      have hz : q.eval (lam k)=0 := spectralCardinal_other lam j k hkj
      simp [eval_mul,eval_pow,hz]
    · simp
  rw [hsum] at h
  have hcoef : 0 < w j*(q.eval (lam j))^2 := mul_pos (hw j) (sq_pos_of_ne_zero (spectralCardinal_self_ne_zero lam hinj j))
  have ht : (w j*(q.eval (lam j))^2)*0≤(w j*(q.eval (lam j))^2)*r.eval (lam j) := by
    rw [mul_zero]
    nlinarith [h]
  exact (mul_le_mul_iff_right₀ hcoef).mp ht
end
end krylov.LinearAlgebra
