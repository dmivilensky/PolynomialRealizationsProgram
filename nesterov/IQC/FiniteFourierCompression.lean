import nesterov.IQC.Certificate
import polyak.General.IQC.KernelL2
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Exact finite-dimensional Fourier compression of arbitrary Hilbert-valued
signal prefixes. Both channels use one finite spatial subspace and one
isometry; every coefficient and cross term of the IQC is preserved.
-/
namespace nesterov.IQC
noncomputable section
open scoped BigOperators
open polyak.General.IQC polyak.General.IQC.Fourier polyak.Energy

section Isometry
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem pairQuadratic_isometry (J : E→ₗᵢ[ℝ]F) (δ : ℝ) (x y σ τ : E) :
    pairQuadratic δ (J x) (J y) (J σ) (J τ)=pairQuadratic δ x y σ τ := by
  simp only [pairQuadratic,←map_sub,←map_add,J.norm_map,J.inner_map_map]

theorem starQuadratic_isometry (J : E→ₗᵢ[ℝ]F) (δ : ℝ) (x σ : E) :
    starQuadratic δ (J x) (J σ)=starQuadratic δ x σ := by
  simp only [starQuadratic,J.norm_map,J.inner_map_map]

theorem zCertificateQuadratic_isometry {a : Spectral.SymbolPair} {t : ℝ}
    (cert : Duality.StrictCertificate a t) (J : E→ₗᵢ[ℝ]F) (x σ : ℤ→E) (k : ℤ) :
    zCertificateQuadratic (transported cert) (fun j=>J (x j)) (fun j=>J (σ j)) k=
      zCertificateQuadratic (transported cert) x σ k := by
  simp only [zCertificateQuadratic,←map_smul,pairQuadratic_isometry,starQuadratic_isometry]

theorem certificateForm_isometry {a : Spectral.SymbolPair} {t : ℝ}
    (cert : Duality.StrictCertificate a t) (J : E→ₗᵢ[ℝ]F)
    (x σ : ZSpace E) (y τ : ZSpace F)
    (hx : ∀ k,J (x k)=y k) (hσ : ∀ k,J (σ k)=τ k) :
    certificateForm (transported cert) (x,σ) (x,σ)=
      certificateForm (transported cert) (y,τ) (y,τ) := by
  rw [certificateForm_eq_tsum,certificateForm_eq_tsum]
  apply tsum_congr
  intro k
  have he:=zCertificateQuadratic_isometry cert J (fun j=>x j) (fun j=>σ j) k
  simpa only [hx,hσ] using he.symm

end Isometry

section Compression
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Two arbitrary finite signal prefixes have exact common Euclidean
coordinates, including every inner product between the two channels. -/
theorem exists_finite_fourier_compression (S : Finset ℤ) (x σ : ZSpace E) :
    ∃ d : ℕ,∃ y τ : ZSpace (EuclideanSpace ℝ (Fin d)),
      ∃ J : EuclideanSpace ℝ (Fin d)→ₗᵢ[ℝ]E,
        (∀ k,J (y k)=zCutoff S x k) ∧ (∀ k,J (τ k)=zCutoff S σ k) := by
  classical
  let a : S×Fin 2→E:=fun i=>if i.2=0 then x i.1 else σ i.1
  let V : Submodule ℝ E:=Submodule.span ℝ (Set.range a)
  have : FiniteDimensional ℝ V:=FiniteDimensional.span_of_finite ℝ (Set.finite_range a)
  let e:=(stdOrthonormalBasis ℝ V).repr
  let d:=Module.finrank ℝ V
  let J : EuclideanSpace ℝ (Fin d)→ₗᵢ[ℝ]E:=V.subtypeₗᵢ.comp e.symm.toLinearIsometry
  have hx (k : ℤ) : zCutoff S x k∈V := by
    by_cases hk : k∈S
    · rw [zCutoff_apply,ite_eq_left hk]
      exact Submodule.subset_span ⟨(⟨k,hk⟩,0),by simp [a]⟩
    · rw [zCutoff_apply,ite_eq_right hk]
      exact V.zero_mem
  have hσ (k : ℤ) : zCutoff S σ k∈V := by
    by_cases hk : k∈S
    · rw [zCutoff_apply,ite_eq_left hk]
      exact Submodule.subset_span ⟨(⟨k,hk⟩,1),by simp [a]⟩
    · rw [zCutoff_apply,ite_eq_right hk]
      exact V.zero_mem
  let y0 : ℤ→EuclideanSpace ℝ (Fin d):=fun k=>e ⟨zCutoff S x k,hx k⟩
  let τ0 : ℤ→EuclideanSpace ℝ (Fin d):=fun k=>e ⟨zCutoff S σ k,hσ k⟩
  have hy : ZSquareSummable y0 := by
    have he : (fun k=>‖y0 k‖^2)=(fun k=>‖zCutoff S x k‖^2):=by
      funext k
      simp only [y0,e.norm_map]
      rfl
    rw [ZSquareSummable,he]
    exact zlp_squareSummable (zCutoff S x)
  have hτ : ZSquareSummable τ0 := by
    have he : (fun k=>‖τ0 k‖^2)=(fun k=>‖zCutoff S σ k‖^2):=by
      funext k
      simp only [τ0,e.norm_map]
      rfl
    rw [ZSquareSummable,he]
    exact zlp_squareSummable (zCutoff S σ)
  refine ⟨d,toZL2 y0 hy,toZL2 τ0 hτ,J,?_,?_⟩
  · intro k
    change ((e.symm (e ⟨zCutoff S x k,hx k⟩):V):E)=zCutoff S x k
    rw [e.symm_apply_apply]
  · intro k
    change ((e.symm (e ⟨zCutoff S σ k,hσ k⟩):V):E)=zCutoff S σ k
    rw [e.symm_apply_apply]

end Compression
end
end nesterov.IQC
