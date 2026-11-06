import chebyshev1.Realization.AffineExecution
import chebyshev1.Stepsize.Basic
import chebyshev1.Prefix.RatioAlgorithm

/-! Affine consistency is proved for the concrete methods, not assumed anew. -/
namespace chebyshev1.TwoTerm
noncomputable section
open scoped BigOperators Matrix

def affineCenter (s : ℕ) : Fin 2 → ℝ := if s=0 then ![1,0] else ![1,1]

def affineConsistency (S : TwoTerm) {N : ℕ}
    (hf : ∀ s, 0<s → s<N → S.a s+S.b s=1) :
    S.realization.AffineConsistent N where
  center := affineCenter
  initial := by simp [affineCenter, realization]
  transition := by
    intro s hs
    by_cases hz : s=0
    · subst s
      ext i
      fin_cases i <;> simp [affineCenter, realization, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · have hs0 : 0<s := Nat.pos_of_ne_zero hz
      ext i
      fin_cases i <;> simp [affineCenter, realization, hz, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two, hf s hs0 hs]
  query := by
    intro s _
    by_cases hz : s=0 <;> simp [affineCenter, realization, hz, dotProduct, Fin.sum_univ_two]
  terminal := by
    by_cases hz : N=0 <;> simp [affineCenter, realization, hz, dotProduct, Fin.sum_univ_two]

end
end chebyshev1.TwoTerm

namespace chebyshev1.Stepsize
noncomputable section
open scoped BigOperators

def affineConsistency (gamma : ℕ → ℝ) (N : ℕ) :
    (realization gamma).AffineConsistent N where
  center := fun _ _ => 1
  initial := rfl
  transition := by intro s _; simp [realization]
  query := by intro s _; simp [realization, dotProduct]
  terminal := by simp [realization, dotProduct]

end
end chebyshev1.Stepsize

namespace chebyshev1.JacobiData
noncomputable section

def affineConsistency (J : JacobiData) (I : SpectralInterval) {N : ℕ}
    (h : J.Admissible I N) : (J.realization I).AffineConsistent N :=
  (J.method I).affineConsistency (by
    intro s hs hsN
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
    exact J.fixed_point I n (h (n+2) (by omega)).ne')

end
end chebyshev1.JacobiData

namespace chebyshev1.Prefix
noncomputable section

def affineConsistency (I : SpectralInterval) (N : ℕ) :
    (realization I).AffineConsistent N := by
  rw [← jacobi_realization I]
  exact jacobiData.affineConsistency I (jacobi_admissible I N)

end
end chebyshev1.Prefix
