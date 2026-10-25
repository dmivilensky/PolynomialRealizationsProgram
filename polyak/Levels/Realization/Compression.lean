import polyak.Levels.Realization.Prefix
import polyak.Interpolation.FiniteSpan
import polyak.Interpolation.Extension
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Article: exact threshold criterion, finite-horizon restriction in Appendix E.
The span contains the actual positions and gradients of the visited prefix.
Interpolation in its orthonormal coordinates produces a genuine Euclidean
objective with the same from-rest prefix norms. The dimension may depend
on the horizon; the original Hilbert-space trajectory does not. -/

namespace polyak.Levels.Realization
noncomputable section
open Interpolation Dynamics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem compress_normalized_run {ψ : E→ℝ} (hψ : NormalizedSmooth ψ)
    {μ L : ℝ} (hμ : 0<μ) (hL : μ<L) (α β : ℝ) (x₀ : E) (hx₀ : x₀≠0) (N : ℕ) :
    ∃ d : ℕ,0<d ∧ ∃ f : EuclideanSpace ℝ (Fin d)→ℝ,
      CenteredSmoothStronglyConvex μ L f ∧
      ∃ y₀,y₀≠0 ∧ ∀ k : ℕ,k≤N→
        ‖iterate (gradient f) α β y₀ k‖=
          ‖iterate (gradient (denormalizeFunction μ L ψ)) α β x₀ k‖ := by
  let e:=iterate (gradient (denormalizeFunction μ L ψ)) α β x₀
  let x : Option (Fin (N+1))→E:=fun i=>i.elim 0 (fun j=>e j)
  let σ : Option (Fin (N+1))→E:=fun i=>gradient ψ (x i)
  let v : Option (Fin (N+1))→ℝ:=fun i=>ψ (x i)
  let S:=dataSpan x σ
  let P : E→L[ℝ]S:=S.orthogonalProjectionOnto
  let J: S→ₗᵢ[ℝ]EuclideanSpace ℝ (Fin (Module.finrank ℝ S)):=
    (stdOrthonormalBasis ℝ S).repr.toLinearIsometry
  let T : E→ₗ[ℝ]EuclideanSpace ℝ (Fin (Module.finrank ℝ S)):=
    J.toLinearMap.comp P.toLinearMap
  let y:=fun i=>J (spanPosition x σ i)
  let s:=fun i=>J (spanGradient x σ i)
  have hTx (i) : T (x i)=y i := by
    change J (P (x i))=J (spanPosition x σ i)
    congr 1
    exact S.orthogonalProjectionOnto_mem_subspace_eq_self (spanPosition x σ i)
  have hTσ (i) : T (σ i)=s i := by
    change J (P (σ i))=J (spanGradient x σ i)
    congr 1
    exact S.orthogonalProjectionOnto_mem_subspace_eq_self (spanGradient x σ i)
  have hnorm (i) : ‖T (x i)‖=‖x i‖ := by rw [hTx]; exact J.norm_map _
  have htable : TableFeasible y s v := by
    intro i j
    rw [datumT_isometry J,datumR_isometry J]
    exact hψ.tableFeasible x i j
  have hy0 : y none=0 := by rw [←hTx]; exact map_zero T
  have hs0 : s none=0 := by rw [←hTσ]; simp [σ,x,hψ.gradient_zero]
  have hv0 : v none=0 := hψ.value_zero
  obtain ⟨Ψ,hΨ,hdata⟩:=exists_normalized_interpolant htable none hy0 hs0 hv0
  have hg (k : ℕ) (hk : k≤N) : gradient Ψ (T (e k))=T (gradient ψ (e k)) := by
    let i : Option (Fin (N+1)):=some ⟨k,by omega⟩
    have hh:gradient Ψ (y i)=s i:=(hdata i).2
    rw [←hTx,←hTσ] at hh
    exact hh
  let f:=denormalizeFunction μ L Ψ
  have hf : CenteredSmoothStronglyConvex μ L f:=hΨ.denormalize hμ hL
  have hgrad (k : ℕ) (hk : k<N) : gradient f (T (e k))=
      T (gradient (denormalizeFunction μ L ψ) (e k)) := by
    rw [(hasGradientAt_denormalize hΨ.differentiable (T (e k))).gradient,
      (hasGradientAt_denormalize hψ.differentiable (e k)).gradient,
      map_sub,map_smul,map_smul,hg k (by omega)]
  have hrun:=iterate_prefix_map T (gradient (denormalizeFunction μ L ψ))
    (gradient f) α β x₀ N hgrad
  let i₀ : Option (Fin (N+1)):=some ⟨0,by omega⟩
  have hn₀ : ‖T x₀‖=‖x₀‖:=hnorm i₀
  have hne : T x₀≠0:=by intro hh; rw [hh,norm_zero] at hn₀; exact hx₀ (norm_eq_zero.mp hn₀.symm)
  have hspan : spanPosition x σ i₀≠0 := by
    intro hh
    have he:=congrArg J hh
    change y i₀=J 0 at he
    rw [←hTx,map_zero] at he
    exact hne he
  let _ : Nontrivial S:=⟨⟨spanPosition x σ i₀,0,hspan⟩⟩
  refine ⟨Module.finrank ℝ S,Module.finrank_pos, f,hf,T x₀,hne,fun k hk=>?_⟩
  rw [hrun k hk]
  exact hnorm (some ⟨k,by omega⟩)

end
end polyak.Levels.Realization
