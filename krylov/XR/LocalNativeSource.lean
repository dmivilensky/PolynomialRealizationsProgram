import krylov.XR.LocalNativeRemainder

/-!
Article: main_krylov, lem:xr-local, assembled actual scalar-source identity.
Use: under the original strict-reference hypotheses, the literal native
algorithm's internal virtual point and true function gradient are exactly
the operator response proved above to satisfy I/E1 with a quadratic
remainder. Every operator coordinate is its true Hessian segment average.
The extra segment hypotheses are solely genuine derivative/continuity
conditions needed for FTC at evaluated and unevaluated segments; they are
not execution, query-bound or output-jet certificates.
-/
namespace krylov.XR
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {n : ℕ}

/-- The actual native source output, including its genuine gradient,
is the assembled I/E1 operator response with its computed native trials. -/
theorem native_XR_local_actual_output (P : Parameters) (hP : P.Valid (n + 1)) (hoff : P.valuesEnabled = false)
    (bounds : SpectralBounds) (hinit : P.initialCapacity = n + 1) (hmax : P.maximumCapacity = n + 1)
    (base : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hb : base.PosDef)
    (g₀ : EuclideanSpace ℝ (Fin (n + 1))) (constant : ℝ)
    (hatoms : referenceAtomCount base hb g₀ = n + 1)
    (htrial : ∀ k < n + 1,
      let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
        (quadraticObjective (cgOperator base) g₀ constant) (quadraticGradient (cgOperator base) g₀) 0 k
      0 < endpointComputedTrial P bounds k C ∧ ContDiffAt ℝ 2 (endpointComputedTrial P bounds k) C)
    (hstrict : ∀ k < n + 1, EndpointTransitionCoreStrict P.armijo
      (P.safeguardMargin * ‖WithLp.ofLp g₀‖⁻¹) (‖WithLp.ofLp g₀‖⁻¹ / P.safeguardMargin)
      (endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds)
        (quadraticObjective (cgOperator base) g₀ constant) (quadraticGradient (cgOperator base) g₀) 0 (k + 1))) :
    ∃ radius epsilon : ℝ, 0 < radius ∧ 0 < epsilon ∧
      ∀ (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
        (G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
        (H : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ]
          EuclideanSpace ℝ (Fin (n + 1))),
        f 0 = constant → G 0 = g₀ →
        (∀ z ∈ ball 0 radius, HasFDerivAt f (innerSL ℝ (G z)) z) →
        (∀ z ∈ ball 0 radius, HasFDerivAt G (H z) z) →
        (∀ z ∈ ball 0 radius, ‖H z - cgOperator base‖ ≤ epsilon) →
        (∀ N ≤ n+1,
          let S := fullVirtualRun P (algorithmTrialParameter P) f G 0 bounds N
          ContinuousOn (fun t : ℝ => H (S.point+t • fullVirtualCorrection P S)) (Icc 0 1)) →
        (∀ N ≤ n+1,
          let S := fullVirtualRun P (algorithmTrialParameter P) f G 0 bounds N
          ∀ t ∈ Icc (0:ℝ) 1, HasFDerivAt G (H (S.point+t • fullVirtualCorrection P S))
            (S.point+t • fullVirtualCorrection P S)) →
        (∀ k<n+1,
          let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G 0 k
          let step := endpointVirtualQuery P.valuesEnabled (endpointComputedTrial P bounds k) C-C.1 (Fin.last k)
          ContinuousOn (fun t : ℝ => H (C.1 (Fin.last k)+t • step)) (Icc 0 1)) →
        (∀ k<n+1,
          let C := endpointFunctionRun P.valuesEnabled (endpointComputedTrial P bounds) f G 0 k
          let step := endpointVirtualQuery P.valuesEnabled (endpointComputedTrial P bounds k) C-C.1 (Fin.last k)
          ∀ t ∈ Icc (0:ℝ) 1, HasFDerivAt G (H (C.1 (Fin.last k)+t • step)) (C.1 (Fin.last k)+t • step)) →
        ∀ N ≤ n+1,
          let x := algorithmVirtualPoint P (algorithmRun P f G 0 bounds N)
          (x,G x) = nativeOperatorOutput P bounds (cgOperator base) g₀ constant N
            (nativeFunctionErrorInputs P bounds (cgOperator base) f G H N) := by
  obtain ⟨radius,epsilon,hr,he,h⟩ := native_XR_local_virtual_outputs P hP bounds hinit hmax base hb
    g₀ constant hatoms htrial hstrict
  refine ⟨radius,epsilon,hr,he,?_⟩
  intro f G H hf hg hF hG hsmall hHo hGo hHs hGs N hN
  have hx := h f G H hf hg hF hG hsmall N hN
  dsimp only
  rw [hx]
  exact (nativeOperatorOutput_actual_gradient P hoff bounds hinit hmax (cgOperator base) g₀ constant
    f G H hg N hN (fun k hk => hHs k (hk.trans_le hN))
    (fun k hk => hGs k (hk.trans_le hN)) (hHo N hN) (hGo N hN)).symm

end
end krylov.XR
