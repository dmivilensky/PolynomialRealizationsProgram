import krylov.LinearAlgebra.MatrixAsymptotics
set_option autoImplicit false
/-!
Article: main_krylov, prop:classical(c), actual inverse comparison.
Use: transfer the proved native quadratic model identity to its genuine
full-basis inverse model and final gradient action.
Source: real matrix inverse continuity on units, the exact resolvent
identity and the original spectral matrix product calculus.
-/

namespace krylov.LinearAlgebra
noncomputable section
open Matrix Filter Topology Asymptotics
open scoped Matrix.Norms.L2Operator
variable {α : Type*} {n : ℕ} {l : Filter α}

/-- Inverting two actual matrices with the same nonsingular limit preserves
their genuine difference order in the original spectral norm.
Use: the actual quadratic direct-model identity yields a quadratic inverse
identity, with all inverse domains derived from the true common limit.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: continuity on the actual unit group bounds both real inverses and
gives their genuine eventual unit domains. The exact resolvent identity
then multiplies the actual difference by those bounded native inverses. -/
theorem matrix_inverse_difference_order (A B : α → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (hC : IsUnit C.det) (s : α → ℝ)
    (hA : Tendsto A l (𝓝 C)) (hB : Tendsto B l (𝓝 C))
    (hAB : (fun z => A z-B z) =O[l] s) :
    (fun z => (A z)⁻¹-(B z)⁻¹) =O[l] s := by
  have hu : IsUnit C := (Matrix.isUnit_iff_isUnit_det _).mpr hC
  have hcont : ContinuousAt (fun M : Matrix (Fin n) (Fin n) ℝ => M⁻¹) C := by
    simpa only [Matrix.nonsing_inv_eq_ringInverse,hu.unit_spec] using NormedRing.inverse_continuousAt hu.unit
  have ha : (fun z => (A z)⁻¹) =O[l] (fun _ => (1 : ℝ)) := (hcont.tendsto.comp hA).isBigO_one ℝ
  have hb : (fun z => (B z)⁻¹) =O[l] (fun _ => (1 : ℝ)) := (hcont.tendsto.comp hB).isBigO_one ℝ
  have h := (ha.mul hAB.neg_left).mul hb
  have h' : (fun z => (A z)⁻¹*(-(A z-B z))*(B z)⁻¹) =O[l] s := by
    simpa only [one_mul,mul_one] using h
  apply h'.congr' ?_ EventuallyEq.rfl
  filter_upwards [hA.eventually (Units.isOpen.mem_nhds hu),hB.eventually (Units.isOpen.mem_nhds hu)] with z haz hbz
  rw [neg_sub,Matrix.inv_sub_inv (by exact ⟨fun _ => hbz,fun _ => haz⟩)]

/-- The actual full-basis inverse congruence is the inverse of the genuine
uncompressed matrix on its real basis and compressed inverse domains.
Use: identify the native quasi-Newton inverse action before comparing it
with the latest-information correction on the same actual pairs.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: multiply the candidate by the actual model; insert the genuine
basis inverse and cancel the real compressed matrix and basis factors. -/
theorem full_basis_inverse_model (S B : Matrix (Fin n) (Fin n) ℝ)
    (hS : IsUnit S.det) (hC : IsUnit (Sᵀ*B*S).det) :
    B⁻¹=S*(Sᵀ*B*S)⁻¹*Sᵀ := by
  apply Matrix.inv_eq_right_inv
  have ht : IsUnit Sᵀ.det := by simpa only [Matrix.det_transpose] using hS
  have he : Sᵀ⁻¹*(Sᵀ*B*S)=B*S := by
    calc
      _ = (Sᵀ⁻¹*Sᵀ)*B*S := by noncomm_ring
      _ = B*S := by rw [Matrix.nonsing_inv_mul _ ht,Matrix.one_mul]
  calc
    _ = (B*S)*(Sᵀ*B*S)⁻¹*Sᵀ := by noncomm_ring
    _ = (Sᵀ⁻¹*(Sᵀ*B*S))*(Sᵀ*B*S)⁻¹*Sᵀ := by rw [he]
    _ = Sᵀ⁻¹*((Sᵀ*B*S)*(Sᵀ*B*S)⁻¹)*Sᵀ := by noncomm_ring
    _ = 1 := by rw [Matrix.mul_nonsing_inv _ hC,Matrix.mul_one,Matrix.nonsing_inv_mul _ ht]

/-- A genuine full-basis quadratic compressed-model comparison gives the
same order for the actual native inverse model and the actual latest
correction operator, with every inverse domain derived from the true limits.
Use: close the original direct Broyden inverse comparison on its own pairs.
Article: main_krylov, prop:classical(c), apE:broyden.
Proof: the actual compressed model has the same nonsingular limit as
the genuine latest model. The proved resolvent estimate preserves their
difference order. The real basis and transpose are bounded by their limit;
the exact full-basis inverse congruence identifies the native inverse. -/
theorem full_basis_inverse_order (S B T : α → Matrix (Fin n) (Fin n) ℝ)
    (S0 T0 : Matrix (Fin n) (Fin n) ℝ) (hS0 : IsUnit S0.det) (hT0 : IsUnit T0.det)
    (s : α → ℝ) (hs : Tendsto s l (𝓝 0)) (hS : Tendsto S l (𝓝 S0))
    (hT : Tendsto T l (𝓝 T0))
    (hdiff : (fun z => (S z)ᵀ*B z*S z-T z) =O[l] s) :
    (fun z => (B z)⁻¹-S z*(T z)⁻¹*(S z)ᵀ) =O[l] s := by
  have hC : Tendsto (fun z => (S z)ᵀ*B z*S z) l (𝓝 T0) := by
    simpa only [sub_add_cancel,zero_add] using (hdiff.trans_tendsto hs).add hT
  have hi := matrix_inverse_difference_order _ T T0 hT0 s hC hT hdiff
  have hb := hS.isBigO_one ℝ
  have hbt := matrix_transpose_bigO S (fun _ => (1 : ℝ)) hb
  have h := matrix_mul_bigO _ _ _ _ (matrix_mul_bigO S _ _ _ hb hi) hbt
  have h' : (fun z => S z*((((S z)ᵀ*B z*S z)⁻¹)-(T z)⁻¹)*(S z)ᵀ) =O[l] s := by
    simpa only [one_mul,mul_one] using h
  apply h'.congr' ?_ EventuallyEq.rfl
  have hSu : IsUnit S0 := (Matrix.isUnit_iff_isUnit_det _).mpr hS0
  have hTu : IsUnit T0 := (Matrix.isUnit_iff_isUnit_det _).mpr hT0
  filter_upwards [hS.eventually (Units.isOpen.mem_nhds hSu),hC.eventually (Units.isOpen.mem_nhds hTu)] with z hSz hCz
  rw [full_basis_inverse_model (S z) (B z)
    ((Matrix.isUnit_iff_isUnit_det _).mp hSz) ((Matrix.isUnit_iff_isUnit_det _).mp hCz)]
  noncomm_ring

end
end krylov.LinearAlgebra
