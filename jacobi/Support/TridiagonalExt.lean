import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic

/-!
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Exact entry comparison for real symmetric tridiagonal matrices.
This elementary helper is used to identify both genuine support
Darboux Gram products with the original and shifted Jacobi matrices.
Use: supportDarboux_original and supportDarboux_shifted identify their complete actual finite matrices from the proved genuine sparse-product formulas.
-/
namespace jacobi.Support
noncomputable section

/-- Real symmetric matrices are equal when their original diagonal, upper adjacent and remaining upper entries agree.
Use: supportDarboux_original and supportDarboux_shifted identify their complete actual finite matrices from the proved genuine sparse-product formulas.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Source: symmetry and extensionality of finite tridiagonal matrices.
Proof: compare each upper entry by its actual equal, adjacent or separated indices. Every lower entry then follows by the two genuine symmetry identities. -/
theorem symmetric_tridiagonal_ext {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsSymm) (hB : B.IsSymm) (hD : ∀ i,A i i=B i i)
    (hU : ∀ i j:Fin n,(i:ℕ)+1=(j:ℕ) → A i j=B i j)
    (hF : ∀ i j:Fin n,(i:ℕ)+1<(j:ℕ) → A i j=B i j) : A=B := by
  -- Each actual finite entry is recovered from the original upper triangular data and real symmetry.
  have h (i j:Fin n) (hij:i≤j) : A i j=B i j := by
    by_cases he : i=j
    · subst j; exact hD i
    by_cases hu : (i:ℕ)+1=(j:ℕ)
    · exact hU i j hu
    · exact hF i j (by have hn : (i:ℕ)≠(j:ℕ) := fun h => he (Fin.ext h); omega)
  ext i j
  rcases le_total i j with hij|hji
  · exact h i j hij
  · exact (hA.apply i j).symm.trans ((h j i hji).trans (hB.apply i j))

end
end jacobi.Support
