import krylov.Envelope.CanonicalPolynomialFlags
import krylov.Envelope.DirectionResponse

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(b), actual continuation-direction tilt orthogonality.
Use: construct the genuine measured direction-polynomial tilt vectors and
prove their real old-flag orthogonality from the actual chronological
polynomial degree bound and true CG error geometry.
Source: standard real symmetric polynomial calculus and genuine actual
CG Krylov flag propagation and orthogonality.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Secant Polynomial Matrix
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The true measured continuation-direction polynomial acting on the actual base image of the genuine reference error.
Use: The true measured continuation-direction polynomial acting on the actual base image of the genuine reference error.
Article: main_krylov, apB:lem:mu(b), actual continuation-direction tilt orthogonality.
Proof: Use the real chronological direction response for the actual earlier gradient injection time. -/
def directionTiltVector (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N i j : ℕ) :
    EuclideanSpace ℝ (Fin n) :=
  (aeval (cgOperator base).toLinearMap (psi (CG.length (cgOperator base) g) (CG.beta (cgOperator base) g)
    (j+1) (i-(j+1)))) (cgOperator base (cgCanonicalError base g N))

/-- Every genuine direction-polynomial tilt vector is orthogonal to its true earlier explored canonical CG flag.
Use: Every genuine direction-polynomial tilt vector is orthogonal to its true earlier explored canonical CG flag.
Article: main_krylov, apB:lem:mu(b), actual continuation-direction tilt orthogonality.
Proof: Combine the actual direction response with the genuine polynomial variable. Its real degree bound places every true old-flag test image inside the actual final explored flag, orthogonal to the genuine CG error. -/
theorem directionTiltVector_orthogonal (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N i j : ℕ) (hcount : N≤referenceAtomCount base hb g)
    (hi : i<N) (hji : j < i) : directionTiltVector base g N i j∈(exploredFlag base g (j+1))ᗮ := by
  -- The genuine extra reference-operator action adds one actual polynomial degree, still within the true final explored CG flag.
  let p := psi (CG.length (cgOperator base) g) (CG.beta (cgOperator base) g) (j+1) (i-(j+1))
  have hd := (continuation_degree (CG.length (cgOperator base) g) (CG.beta (cgOperator base) g) (j+1) (i-(j+1))).2
  have hm : (p*X).natDegree≤p.natDegree+1 := by simpa only [natDegree_X] using (natDegree_mul_le (p := p) (q := X))
  have he : directionTiltVector base g N i j=(aeval (cgOperator base).toLinearMap (p*X)) (cgCanonicalError base g N) := by
    simp only [map_mul,aeval_X,Module.End.mul_apply]
    rfl
  rw [he]
  apply canonical_polynomial_error_orthogonal base hb g N (j+1) hcount
  change p.natDegree≤ i-(j+1) at hd
  omega
end
end krylov.Envelope
