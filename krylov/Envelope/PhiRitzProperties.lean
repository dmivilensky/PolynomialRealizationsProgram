import krylov.Envelope.PhiRitz
import krylov.LinearAlgebra.SpectralContinuationSplits
set_option autoImplicit false
/-!
Article: Proposition B.15 [prop:phi] of krylov.tex.
Use: state real splitting, simple genuine Ritz zeros, positivity and both monotonicity assertions for the original measured CG continuation in a single actual-reference theorem.
Source: genuine measured Schur spectral product, actual finite Ritz endpoints and the proved original-matrix spectral geometry.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.LinearAlgebra Matrix Polynomial
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual measured continuation has all printed real spectral, simple-zero, Ritz enclosure, sign, monotonicity and normalization properties.
Use: The actual measured continuation has all printed real spectral, simple-zero, Ritz enclosure, sign, monotonicity and normalization properties.
Article: main_krylov, prop:phi(a), complete actual continuation spectral properties.
Proof: Combine the genuine real Schur factorization with actual attained Ritz endpoints; use positive reciprocal factors and true suffix dimension for strict monotonicity. -/
theorem lanczos_phi_ritz_properties (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (m : ℕ) [Nonempty (Fin m)]
    (hpre : ∀ i<m,CG.gradient Q g i≠0) (j : ℕ) (hj : j≤m) :
    let hT := CG.lanczosMatrix_posDef Q hQ hpos g m hpre
    let P := phi (CG.length Q g) (CG.beta Q g) j (m-j)
    P.Splits ∧
      (∀ lam,P.eval lam=0 → lam∈Set.Icc (spectralLower _ hT.1) (spectralUpper _ hT.1) ∧
        P.derivative.eval lam≠0) ∧
      (∀ lam< spectralLower _ hT.1,0 < P.eval lam) ∧
      AntitoneOn (fun lam => P.eval lam) (Set.Iio (spectralLower _ hT.1)) ∧
      (j<m → StrictAntiOn (fun lam => P.eval lam) (Set.Iio (spectralLower _ hT.1))) ∧
      P.eval 0=1 := by
  -- Every assertion refers to the same original measured continuation and its genuine computed Lanczos spectrum.
  dsimp only
  have hT := CG.lanczosMatrix_posDef Q hQ hpos g m hpre
  let a := spectralLower _ hT.1
  let b := spectralUpper _ hT.1
  have ha : 0 < a := spectralLower_pos _ hT
  have hb : 0 < b := spectralUpper_pos _ hT
  have hlo := spectralLower_le _ hT.1
  have hhi := le_spectralUpper _ hT.1
  -- Real splitting excludes nonreal zeros; the actual Schur spectrum supplies the genuine simple Ritz roots.
  refine ⟨?_,?_,?_,?_,?_,phi_at_zero _ _ _ _⟩
  · rw [lanczos_phi_spectral Q hQ hpos g m hpre j hj]
    exact spectralContinuation_splits _ _
  · intro lam hz
    exact ⟨lanczos_phi_ritz_interval Q hQ hpos g m hpre j hj lam hz,
      lanczos_phi_simple_zero Q hQ hpos g m hpre j hj lam hz⟩
  · intro lam hlam
    exact lanczos_phi_positive_below Q hQ hpos g m hpre j hj a b ha hb hlo hhi lam hlam
  · intro x _ y hy hxy
    exact lanczos_phi_antitone_below Q hQ hpos g m hpre j hj a b ha hb hlo hhi x y hxy hy
  · intro hjm x _ y hy hxy
    exact lanczos_phi_strictAnti_below Q hQ hpos g m hpre j hjm a b ha hb hlo hhi x y hxy hy
end
end krylov.Envelope
