import krylov.XR.LocalQuadraticDomains

/-!
Article: main_krylov, lem:xr-local, complete native reference regularity.
Use: discharge every reference inverse-domain hypothesis of the finite
endpoint program from a true nonstagnating positive quadratic. The only
smoothness hypothesis is the printed primitive positive C² trial rule,
here literally Algorithm XR's actual observable trial function.
Source: the proved quadratic execution invariant and actual chart identity.
-/

namespace krylov.XR
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {n : ℕ}

/-- The full virtual reference trial is exactly its actual endpoint-data
trial, including the true running spectral bounds. -/
theorem fullVirtualRun_trial_endpoint (P : Parameters) (bounds : SpectralBounds)
    (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x₀ : EuclideanSpace ℝ (Fin n)) (k : ℕ) (hk : k ≤ n) :
    algorithmTrialParameter P (fullVirtualRun P (algorithmTrialParameter P) f G x₀ bounds k) =
      endpointComputedTrial P bounds k
        (endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G x₀ k) := by
  rw [fullVirtualRun_eq_endpointNativeState P bounds hinit hmax f G x₀ k hk]
  rfl

/-- Positive primitive trial lengths and true n-atom quadratic data supply
every algebraic domain needed to differentiate the actually executed
full-memory finite query program. No trajectory smoothness or successful
window-test premise is left in this statement. -/
theorem quadratic_endpointProgram_domains (P : Parameters) (bounds : SpectralBounds)
    (hinit : P.initialCapacity = n) (hmax : P.maximumCapacity = n)
    (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v, v ≠ 0 → 0 < inner ℝ v (Q v))
    (g₀ : EuclideanSpace ℝ (Fin n)) (constant : ℝ)
    (hg : ∀ i < n, CG.gradient Q g₀ i ≠ 0)
    (htrial : ∀ k < n,
      let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
        (quadraticObjective Q g₀ constant) (quadraticGradient Q g₀) 0 k
      0 < endpointComputedTrial P bounds k C ∧ ContDiffAt ℝ 2 (endpointComputedTrial P bounds k) C) :
    ∀ k < n, EndpointProgramDomain P.valuesEnabled (endpointComputedTrial P bounds) 0 constant g₀ 2 k
      (adaptiveTranscript (endpointProgramQuery P.valuesEnabled (endpointComputedTrial P bounds) 0 constant g₀)
        (fun x => (quadraticObjective Q g₀ constant x, quadraticGradient Q g₀ x)) k) := by
  let f := quadraticObjective Q g₀ constant
  let G := quadraticGradient Q g₀
  let query := endpointProgramQuery P.valuesEnabled (endpointComputedTrial P bounds) 0 constant g₀
  let oracle := fun x => (f x, G x)
  have hf₀ : f 0 = constant := by
    simp [f, quadraticObjective, krylov.Functions.quadraticPotential]
  have hg₀ : G 0 = g₀ := by simp [G, quadraticGradient]
  have hchart (k : ℕ) : endpointProgramChart P.valuesEnabled (endpointComputedTrial P bounds) 0 constant g₀ k
      (adaptiveTranscript query oracle k) =
      endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G 0 k := by
    have hh := endpointFunctionRun_eq_program P.valuesEnabled (endpointComputedTrial P bounds) f G 0 k
    rw [hf₀, hg₀] at hh
    exact hh.symm
  have hnonzero (k : ℕ) (hk : k < n) : algorithmTrialParameter P
      (fullVirtualRun P (algorithmTrialParameter P) f G 0 bounds k) ≠ 0 := by
    rw [fullVirtualRun_trial_endpoint P bounds hinit hmax f G 0 k hk.le]
    exact (htrial k hk).1.ne'
  have hlocal (k : ℕ) (hk : k < n) :
      let C := endpointProgramChart P.valuesEnabled (endpointComputedTrial P bounds) 0 constant g₀ k
        (adaptiveTranscript query oracle k)
      ContDiffAt ℝ 2 (endpointComputedTrial P bounds k) C ∧
        (∀ i, inner ℝ (endpointStep C i) (endpointImage C i) ≠ 0) ∧
        (endpointVirtualModel P.valuesEnabled C).det ≠ 0 ∧
        (crossGram (endpointImage C) (endpointStep C)).det ≠ 0 := by
    dsimp only
    rw [hchart]
    have hd := fullVirtualRun_quadratic_endpoint_domains P hinit hmax Q hQ hpos g₀ constant bounds
      hg hnonzero k hk.le
    refine ⟨(htrial k hk).2, fun i => (hd.2.1 i).ne', ?_, hd.2.2.2.1⟩
    exact isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det _).mp (hd.2.2.1 P.valuesEnabled).isUnit)
  intro k hk
  induction k with
  | zero => exact hlocal 0 hk
  | succ k ih =>
    refine ⟨?_, hlocal (k + 1) hk⟩
    change EndpointProgramDomain P.valuesEnabled (endpointComputedTrial P bounds) 0 constant g₀ 2 k
      (Fin.init (adaptiveTranscript query oracle (k + 1)))
    simpa only [adaptiveTranscript, Fin.init_snoc] using ih (by omega)

end
end krylov.XR
