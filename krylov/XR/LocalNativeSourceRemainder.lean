import krylov.XR.LocalNativeSource

/-!
Article: main_krylov, lem:xr-local, actual-source I/E1 quadratic expansion.
Use: assemble literal native execution, actual Hessian integral coordinates,
proved primitive trial regularity, and the full operator-ball Taylor theorem.
The radius and quadratic constant precede the actual scalar source.
-/
namespace krylov.XR
noncomputable section
open Matrix Set Metric Filter Topology krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {n : ℕ}

/-- The actual native virtual point and genuine function gradient have the
complete fixed-reference I/E1 first variation with a uniform quadratic
remainder in their true segment-operator inputs. -/
theorem native_XR_local_actual_quadratic_remainder (P : Parameters) (hP : P.Valid (n + 1)) (hoff : P.valuesEnabled = false)
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
        (quadraticObjective (cgOperator base) g₀ constant) (quadraticGradient (cgOperator base) g₀) 0 (k + 1)))
    (N : ℕ) (hN : N ≤ n+1) :
    let Q := cgOperator base
    let tau₀ := nativeOperatorTrialVector P bounds Q g₀ constant N 0
    let L := fderiv ℝ (fun e => prescribedXRFCOutput Q g₀ N (e,tau₀)) 0
    ∃ radius epsilon delta C : ℝ, 0 < radius ∧ 0 < epsilon ∧ 0 < delta ∧ 0 ≤ C ∧
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
        let e := nativeFunctionErrorInputs P bounds Q f G H N
        ‖e‖ ≤ delta →
        let x := algorithmVirtualPoint P (algorithmRun P f G 0 bounds N)
        ‖(x,G x)-(CG.displacement Q g₀ N,CG.gradient Q g₀ N)-L e‖ ≤ C*‖e‖^2 := by
  let Q := cgOperator base
  have hQ := cgOperator_positive base hb
  have hgref : ∀ i<n+1, CG.gradient Q g₀ i ≠ 0 := by
    simpa only [hatoms] using cg_nonstagnation base hb g₀
  obtain ⟨radius,epsilon,hr,he,hsource⟩ := native_XR_local_actual_output P hP hoff bounds hinit hmax base hb
    g₀ constant hatoms htrial hstrict
  obtain ⟨delta,C,hd,hC,hbound⟩ := native_operator_prefix_quadratic_remainder P bounds hinit hmax Q
    hQ.1 hQ.2 g₀ constant hgref htrial N hN
  have hposTau := nativeOperatorTrialVector_zero_pos P bounds Q g₀ constant N
    (fun k hk => (htrial k (hk.trans_le hN)).1)
  have hzero : nativeOperatorOutput P bounds Q g₀ constant N 0 =
      (CG.displacement Q g₀ N,CG.gradient Q g₀ N) :=
    prescribedXRFCOutput_zero Q hQ.1 hQ.2 g₀ N (fun i hi => hgref i (hi.trans_le hN))
      _ (fun i => (hposTau i).ne')
  refine ⟨radius,epsilon,delta,C,hr,he,hd,hC,?_⟩
  intro f G H hf hg hF hG hsmall hHo hGo hHs hGs
  dsimp only
  intro hinput
  have hx := hsource f G H hf hg hF hG hsmall hHo hGo hHs hGs N hN
  have hbnd := hbound (nativeFunctionErrorInputs P bounds Q f G H N) hinput
  rw [←hx,hzero] at hbnd
  exact hbnd

end
end krylov.XR
