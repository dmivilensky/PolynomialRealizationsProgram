import jacobi.Support.DarbouxShifted
import jacobi.Support.EndpointDeletion
import jacobi.Support.NaturalNodes
import jacobi.Support.Persymmetry
import jacobi.Finite.Persymmetric

/-!
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
The actual original trigonometric support chain has exactly its original
cosine lattice as its entire spectrum, throughout the full parameter
range. A proved real Darboux deletion determines the whole characteristic
polynomial, including the exceptional parameters of the cited AW route.
The existing finite uniqueness theorem then identifies the actual chain
with the canonical reciprocal-derivative reconstruction.
Use: naturalChain_charpoly determines the full genuine original cosine spectrum by induction over the actual dimension.
-/
namespace jacobi.Support
noncomputable section
open Real Matrix Polynomial jacobi.Reference chebyshev2 jacobi.Finite

/-- The original support characteristic polynomial has the exact original top-node deletion into the actual alpha-shifted smaller support characteristic.
Use: naturalChain_charpoly determines the full genuine original cosine spectrum by induction over the actual dimension.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Source: the original finite endpoint Darboux factorization and Sylvester's determinant identity.
Proof: both genuine rectangular Gram identities were proved for the original sine coefficients, and the proved general endpoint-deletion theorem applies without any additional spectral premise. -/
theorem naturalChain_charpoly_deletion (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) :
    (naturalChain a b ha hb (n+1)).matrix.charpoly=
      (X-C (cos (gamma a*step a b (n+1))))*
        (naturalChain (a+2) b (by linarith) hb n).matrix.charpoly :=
  endpoint_charpoly_deletion (supportDarbouxFactor a b n) _ _ _
    (supportDarboux_original a b ha hb n) (supportDarboux_shifted a b ha hb n)

/-- The actual alpha-shifted smaller cosine lattice is exactly the original lattice after deleting its first node.
Use: naturalChain_charpoly reconstructs the original whole characteristic product in precisely its genuine source enumeration.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the genuine step is unchanged, gamma_alpha increases by one and the original remaining index increases by one. -/
theorem naturalNode_darboux (a b : ℝ) (n k : ℕ) :
    naturalNode (a+2) b n k=naturalNode a b (n+1) (k+1) := by
  rw [naturalNode,naturalNode,modelAngle_step,modelAngle_step,step_darboux]
  congr 1
  dsimp [gamma]
  push_cast
  ring

/-- The actual original support characteristic polynomial is exactly the full original cosine-node product in every dimension and for every original admissible parameter pair.
Use: naturalChain_spectrum and naturalChain_canonical discharge the support spectrum and canonical original spectral-weight identifications needed by the finite Gram limit.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: induct on the genuine finite dimension. The actual rectangular Darboux identity removes precisely the first original cosine factor and replaces the remaining matrix by the actual shifted smaller support chain. Its genuine shifted lattice is exactly the remaining original lattice, so induction gives the literal original product. -/
theorem naturalChain_charpoly (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) :
    (naturalChain a b ha hb n).matrix.charpoly=(naturalNodes a b ha hb n).polynomial := by
  -- The actual sine-coefficient factorization supplies the induction, so no AW polynomial or generic-position theorem is assumed.
  induction n generalizing a b with
  | zero => simp [Jacobi.matrix,chebyshev1.JacobiData.matrix,Nodes.polynomial]
  | succ n ih =>
    rw [naturalChain_charpoly_deletion,ih (a+2) b (by linarith) hb]
    change (X-C (cos (gamma a*step a b (n+1))))*
      (∏ i:Fin n,(X-C (naturalNode (a+2) b n i)))=
        ∏ i:Fin (n+1),(X-C (naturalNode a b (n+1) i))
    rw [Fin.prod_univ_succ]
    have h0 : naturalNode a b (n+1) 0=cos (gamma a*step a b (n+1)) := by
      rw [naturalNode,modelAngle_step]
      simp only [Nat.cast_zero,zero_add]
    simp only [Fin.val_zero,Fin.val_succ,h0,naturalNode_darboux]

/-- The original support matrix belongs to the previously verified finite fibre with exactly its genuine original cosine nodes.
Use: naturalChain_spectrum and the canonical finite reconstruction reuse the earlier original fibre and weight machinery directly.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: combine the actual original strict interior coupling theorem with its independently proved whole characteristic-node product. -/
theorem naturalChain_inFiber (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) :
    InFiber (naturalChain a b ha hb n) (naturalNodes a b ha hb n).polynomial :=
  ⟨naturalChain_irreducible a b ha hb n,naturalChain_charpoly a b ha hb n⟩

/-- The actual original support matrix has exactly the full original cosine lattice spectrum, without extra or missing eigenvalues and throughout the entire original parameter range.
Use: support weights and polynomials are those of this same original finite support matrix in the finite-to-continuum theorem.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: apply the existing arbitrary-fibre spectral theorem to the proved actual original whole characteristic and strict coupling identities. -/
theorem naturalChain_spectrum (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) :
    spectrum ℝ (naturalChain a b ha hb n).matrix=Set.range (fun i:Fin n => naturalNode a b n i) :=
  (naturalNodes a b ha hb n).spectrum_eq (naturalChain_inFiber a b ha hb n)

/-- The actual original support chain is the existing canonical persymmetric reconstruction of its genuine original cosine-node fibre.
Use: the support weight and polynomial identities can use the earlier actual discrete-measure reconstruction without a separate asserted spectral measure.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: the original chain has its proved actual spectrum and physical persymmetry. The earlier complete finite uniqueness theorem therefore identifies it with the original canonical reconstruction in that exact fibre. -/
theorem naturalChain_canonical (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) :
    naturalChain a b ha hb (n+1)=(persymmetricFiber (naturalNodes a b ha hb (n+1))).val := by
  let J : Fiber (n+1) (naturalNodes a b ha hb (n+1)).polynomial :=
    ⟨naturalChain a b ha hb (n+1),naturalChain_inFiber a b ha hb (n+1)⟩
  have h : J=persymmetricFiber (naturalNodes a b ha hb (n+1)) :=
    (exists_unique_persymmetric (naturalNodes a b ha hb (n+1))).unique
    (naturalChain_persymmetric a b ha hb (n+1))
    (persymmetricFiber_symmetric (naturalNodes a b ha hb (n+1)))
  exact congrArg Subtype.val h

end
end jacobi.Support
