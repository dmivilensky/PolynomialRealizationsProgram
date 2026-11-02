import krylov.XR.LocalQuadraticProgram
import krylov.XR.LocalHistoryTests

/-!
Article: main_krylov, lem:xr-local, derived true reference domains.
Use: obtain every endpoint-chart inverse domain and strict model test
from the actual nonstagnating quadratic execution. These facts are proved
from the primitive positive quadratic and nonzero actual trials, rather
than appended to the local-equivalence source assumptions.
Source: the genuine executed Krylov invariant and exact endpoint dictionary.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant
open scoped InnerProductSpace ComplexOrder
variable {n : ℕ}

/-- All real reference solves and strict scalar/complex model gates of
the full virtual program are consequences of its true quadratic data. -/
theorem fullVirtualRun_quadratic_endpoint_domains (P : Parameters)
    (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant : ℝ) (bounds : SpectralBounds)
    (hg : ∀ i < n, CG.gradient Q g₀ i ≠ 0)
    (htrial : ∀ k < n, algorithmTrialParameter P
      (fullVirtualRun P (algorithmTrialParameter P) (quadraticObjective Q g₀ constant)
        (quadraticGradient Q g₀) 0 bounds k) ≠ 0)
    (k : ℕ) (hk : k ≤ n) :
    let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
      (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 k
    LinearIndependent ℝ (endpointStep C) ∧
      (∀ i, 0 < inner ℝ (endpointStep C i) (endpointImage C i)) ∧
      (∀ values, (endpointVirtualModel values C).PosDef) ∧
      (crossGram (endpointImage C) (endpointStep C)).det ≠ 0 ∧
      (∀ values, (endpointHermitianTest P.windowThreshold values C).PosDef) ∧
      ∀ i, |12 * endpointSplit C i * endpointDefect C i| <
        inner ℝ (endpointStep C i) (endpointImage C i) / 2 := by
  let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
    (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 k
  let S := endpointNativeState P bounds C
  let e := finCongr (endpointObservations_length C)
  have hS : QuadraticEventInvariant Q g₀ constant S k := by
    have hh := fullVirtualRun_quadratic_invariant P hinit hmax Q hQ hpos g₀ constant bounds hg htrial k hk
    rw [fullVirtualRun_eq_endpointNativeState P bounds hinit hmax _ _ 0 k hk] at hh
    exact hh
  have hLIstored : LinearIndependent ℝ (storedSteps (endpointObservations C)) := hS.independent
  have hLI : LinearIndependent ℝ (endpointStep C) := by
    have hh := hLIstored.comp e.symm e.symm.injective
    rw [endpointObservations_steps] at hh
    change LinearIndependent ℝ (endpointStep C ∘ e ∘ e.symm) at hh
    simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using hh
  have hpair : (storedPairing (endpointObservations C)).PosDef :=
    storedPairing_quadratic_posDef Q hQ hpos g₀ constant S.point _ hS.faithful hLIstored
  have hraw : (crossGram (endpointStep C) (endpointImage C)).PosDef := by
    have hh := hpair.submatrix e.symm.injective
    rw [endpointObservations_pairing, submatrix_submatrix] at hh
    change ((crossGram (endpointStep C) (endpointImage C)).submatrix (e ∘ e.symm) (e ∘ e.symm)).PosDef at hh
    simpa only [Equiv.self_comp_symm, submatrix_id_id] using hh
  have hd (i : Fin k) : endpointDefect C i = 0 := by
    have hh := faithful_quadratic_defect Q hQ g₀ constant S.point
      ((endpointObservations C).get (e.symm i))
      (hS.faithful _ (List.get_mem _ (e.symm i)))
    rw [endpointObservations_get] at hh
    change endpointDefect C (e (e.symm i)) = 0 at hh
    simpa only [Equiv.apply_symm_apply] using hh
  have hmodel (values : Bool) : endpointVirtualModel values C =
      crossGram (endpointStep C) (endpointImage C) := by
    simp only [endpointVirtualModel, hd, mul_zero, ite_self, diagonal_zero, sub_zero,
      latest_eq_of_isSymm hraw.isHermitian.isSymm]
  have htranspose : crossGram (endpointImage C) (endpointStep C) =
      (crossGram (endpointStep C) (endpointImage C))ᵀ := by
    ext i j
    exact real_inner_comm _ _
  have hY : (crossGram (endpointImage C) (endpointStep C)).det ≠ 0 := by
    rw [htranspose, hraw.isHermitian.isSymm.eq]
    exact isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det _).mp hraw.isUnit)
  have hcomplex (values : Bool) : (endpointHermitianTest P.windowThreshold values C).PosDef := by
    have hdef : defect (crossGram (endpointStep C) (endpointImage C)) = 0 := by
      rw [defect, hraw.isHermitian.isSymm.eq, sub_self]
    have hzero : (0 : Matrix (Fin k) (Fin k) ℝ).map Complex.ofReal = 0 := by
      ext i j
      exact Complex.ofReal_zero
    simp only [endpointHermitianTest, hmodel, hdef, hzero, smul_zero, add_zero]
    exact ofReal_posDef _ hraw
  refine ⟨hLI, fun i => hraw.diag_pos, fun values => ?_, hY, hcomplex, fun i => ?_⟩
  · rw [hmodel]
    exact hraw
  · rw [hd, mul_zero, abs_zero]
    exact half_pos hraw.diag_pos

end
end krylov.XR
