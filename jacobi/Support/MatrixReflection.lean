import jacobi.Support.ParameterReflection
import jacobi.Finite.AlternatingConjugation

/-!
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
The actual support matrix satisfies the original alternating-conjugation
formula, with the literal physical alternating matrix and the original
parameter-swapped chain on its two sides.
Use: the actual left-edge spectrum and support waves are the reflected right-edge data, yielding the original alternating beta contribution to the Gram limit.
-/
namespace jacobi.Support
noncomputable section
open jacobi.Finite

/-- The original support chains with exchanged endpoint parameters satisfy exactly the printed matrix alternating-conjugation identity.
Use: the actual left-edge spectrum and support waves are the reflected right-edge data, yielding the original alternating beta contribution to the Gram limit.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: actual persymmetric fibre uniqueness proves the support parameter swap, and the genuine reflection has already been proved to be this exact physical matrix conjugation. -/
theorem naturalChain_swap_matrix (a b : ℝ) (ha : -1<a) (hb : -1<b) (n : ℕ) :
    (naturalChain b a hb ha (n+1)).matrix=
      -(alternatingMatrix (n+1)*(naturalChain a b ha hb (n+1)).matrix*alternatingMatrix (n+1)) := by
  rw [naturalChain_swap]
  exact reflect_matrix _

end
end jacobi.Support
