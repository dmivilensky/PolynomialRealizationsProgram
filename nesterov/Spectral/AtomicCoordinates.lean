import nesterov.Spectral.Finite
import Mathlib.LinearAlgebra.Lagrange

/-! For distinct positive atoms, the actual quotient space L²(ν;ℂ) is
isometrically the article's C^J, hence literal R^(2J). The construction uses
continuous Lagrange basis functions and respects the original L² classes. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal ENNReal
namespace nesterov.Spectral
variable {J : Type*} [Fintype J]

private def nodalBasis (c : J→Frequency) (j : J) : C(Frequency,ℂ) := by
  classical
  exact ⟨fun x=>(Lagrange.basis Finset.univ (fun i=>((c i:ℝ):ℂ)) j).eval ((x:ℝ):ℂ),by
    fun_prop⟩

private theorem nodalBasis_self (c : J→Frequency) (hc : Function.Injective c) (j : J) :
    nodalBasis c j (c j)=1 := by
  classical
  apply Lagrange.eval_basis_self _ (Finset.mem_univ j)
  intro i _ k _ he
  apply hc
  exact Subtype.ext (Complex.ofReal_injective he)

private theorem nodalBasis_other (c : J→Frequency) {i j : J} (hij : i≠j) :
    nodalBasis c i (c j)=0 := by
  classical
  change (Lagrange.basis Finset.univ (fun i=>((c i:ℝ):ℂ)) i).eval ((c j:ℝ):ℂ)=0
  exact Lagrange.eval_basis_of_ne (v:=fun i=>((c i:ℝ):ℂ))
    (s:=Finset.univ) hij (Finset.mem_univ j)

private def atomicExtension (w : J→ℝ≥0) (c : J→Frequency) :
    EuclideanSpace ℂ J →ₗ[ℝ] C(Frequency,ℂ) := by
  classical
  refine {
    toFun := fun (v : EuclideanSpace ℂ J)=>
      ∑ j,((Real.sqrt (w j:ℝ):ℂ)⁻¹*v j) • nodalBasis c j
    map_add' := ?_
    map_smul' := ?_ }
  · intro v v'
    ext x
    simp only [ContinuousMap.sum_apply,ContinuousMap.add_apply,ContinuousMap.smul_apply,
      PiLp.add_apply,smul_eq_mul]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · intro a v
    ext x
    simp only [ContinuousMap.sum_apply,ContinuousMap.smul_apply,PiLp.smul_apply,
      Complex.real_smul,Finset.smul_sum,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro j _
    ring

private theorem atomicExtension_value (w : J→ℝ≥0) (c : J→Frequency)
    (hc : Function.Injective c) (v : EuclideanSpace ℂ J) (j : J) :
    atomicExtension w c v (c j)=(Real.sqrt (w j:ℝ):ℂ)⁻¹*v j := by
  classical
  simp only [atomicExtension,LinearMap.coe_mk,AddHom.coe_mk,ContinuousMap.sum_apply,
    ContinuousMap.smul_apply,smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · rw [nodalBasis_self c hc,mul_one]
  · intro i _ hij
    rw [nodalBasis_other c hij,mul_zero]
  · simp

private theorem finiteLift_atomicExtension (w : J→ℝ≥0) (c : J→Frequency)
    (hw : ∀ j,0<w j) (hc : Function.Injective c) (v : EuclideanSpace ℂ J) :
    finiteLift w c (atomicExtension w c v)=v := by
  apply PiLp.ext
  intro j
  change (Real.sqrt (w j:ℝ):ℂ)*atomicExtension w c v (c j)=v j
  rw [atomicExtension_value w c hc,←mul_assoc,mul_inv_cancel₀,one_mul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hw j)).ne'

/-- The weighted coordinate embedding into the actual atomic L² quotient. -/
def atomicEmbedding (w : J→ℝ≥0) (c : J→Frequency) (hw : ∑ j,w j=1)
    (hpos : ∀ j,0<w j) (hc : Function.Injective c) :
    EuclideanSpace ℂ J →ₗᵢ[ℝ] WaveSpace (finiteSpectrum w c hw) where
  toLinearMap := (lift (finiteSpectrum w c hw)).toLinearMap.comp (atomicExtension w c)
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have hh := polyak.Waves.norm_sq_finiteLift_eq_lift w c hw (atomicExtension w c v)
    rw [finiteLift_atomicExtension w c hpos hc] at hh
    exact hh.symm

theorem atomicEmbedding_surjective (w : J→ℝ≥0) (c : J→Frequency) (hw : ∑ j,w j=1)
    (hpos : ∀ j,0<w j) (hc : Function.Injective c) :
    Function.Surjective (atomicEmbedding w c hw hpos hc) := by
  intro f
  let v : EuclideanSpace ℂ J := WithLp.toLp 2 (fun j=>(Real.sqrt (w j:ℝ):ℂ)*f (c j))
  refine ⟨v,?_⟩
  apply Lp.ext
  have he := (atomicExtension w c v).coeFn_toLp (p:=2) (𝕜:=ℝ)
    (finiteSpectrum w c hw:Measure Frequency)
  apply he.trans
  change ∀ᵐ x ∂(∑ j,(w j:ℝ≥0∞) • Measure.dirac (c j)),atomicExtension w c v x=f x
  rw [ae_finsetSum_measure_iff]
  intro j _
  apply Measure.ae_smul_measure
  simp only [ae_dirac_eq,Filter.eventually_pure]
  rw [atomicExtension_value w c hc]
  change (Real.sqrt (w j:ℝ):ℂ)⁻¹*((Real.sqrt (w j:ℝ):ℂ)*f (c j))=f (c j)
  rw [←mul_assoc,inv_mul_cancel₀,one_mul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hpos j)).ne'

/-- The actual L² space of J distinct positive atoms is C^J isometrically. -/
def atomicCoordinates (w : J→ℝ≥0) (c : J→Frequency) (hw : ∑ j,w j=1)
    (hpos : ∀ j,0<w j) (hc : Function.Injective c) :
    WaveSpace (finiteSpectrum w c hw) ≃ₗᵢ[ℝ] EuclideanSpace ℂ J :=
  (LinearIsometryEquiv.ofSurjective (atomicEmbedding w c hw hpos hc)
    (atomicEmbedding_surjective w c hw hpos hc)).symm

/-- Literal R^(2J) coordinates for the actual quotient L² space. -/
def atomicRealCoordinates (w : J→ℝ≥0) (c : J→Frequency) (hw : ∑ j,w j=1)
    (hpos : ∀ j,0<w j) (hc : Function.Injective c) :
    WaveSpace (finiteSpectrum w c hw) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2*Fintype.card J)) := by
  let e : EuclideanSpace ℂ J ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2*Fintype.card J)) := by
    rw [←finite_real_dimension (J:=J)]
    exact (stdOrthonormalBasis ℝ (EuclideanSpace ℂ J)).repr
  exact (atomicCoordinates w c hw hpos hc).trans e
end nesterov.Spectral
