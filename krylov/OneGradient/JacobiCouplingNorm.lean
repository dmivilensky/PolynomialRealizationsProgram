import krylov.OneGradient.SpectralFibreParameters
set_option autoImplicit false
/-!
Article: main_krylov, s5:fibre(b), actual last-coupling limiting control.
Use: prove that the genuine positive Lanczos coupling, not merely a supplied
matrix entry, tends to zero along a real family approaching a scalar matrix.
Source: the actual orthonormal physical Lanczos frame, its genuine compression
and the ordinary real Cauchy--Schwarz and Euclidean operator norm inequalities.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual positive final Lanczos coupling is controlled by the genuine
spectral distance of the original reference from any real scalar matrix.
Use: scalar limiting families have a genuinely vanishing source beta even
though their actual Lanczos frames need not converge at the degenerate limit.
Article: main_krylov, s5:fibre(b), beta tends to zero.
Proof: two different actual Lanczos vectors are orthonormal, so the scalar
part has zero cross pairing. Bound the remaining original physical matrix
action by real Cauchy--Schwarz and its actual Euclidean operator norm. -/
theorem physical_jacobi_last_coupling_le_scalar_distance
    (A : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+2))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+2) (d : ℝ) :
    physicalJacobi A hA g hg hc (Fin.castSucc (Fin.last n)) (Fin.last (n+1))≤‖A-d • 1‖ := by
  let i : Fin (n+2) := Fin.castSucc (Fin.last n)
  let j : Fin (n+2) := Fin.last (n+1)
  let ii : Fin (activeSpectralValues A hA.1 g).card := ⟨i.val,by rw [hc];exact i.isLt⟩
  let jj : Fin (activeSpectralValues A hA.1 g).card := ⟨j.val,by rw [hc];exact j.isLt⟩
  let u := lanczosVector A hA g hg ii
  let v := lanczosVector A hA g hg jj
  have hij : ii≠jj := by
    intro he
    have hv := congrArg Fin.val he
    change n=n+1 at hv
    omega
  have ho := lanczosVector_orthonormal A hA g hg
  have huv : inner ℝ u v=0 := ho.inner_eq_zero hij
  have hu : ‖u‖=1 := ho.norm_eq_one ii
  have hv : ‖v‖=1 := ho.norm_eq_one jj
  have he : inner ℝ u (cgOperator (A-d • 1) v)=
      physicalJacobi A hA g hg hc i j := by
    rw [physicalJacobi,physical_lanczos_compression]
    change inner ℝ u (cgOperator (A-d • 1) v)=inner ℝ u (cgOperator A v)
    simp only [cgOperator,map_sub,map_smul,map_one,_root_.sub_apply,_root_.smul_apply,
      one_apply_eq_self,inner_sub_right,real_inner_smul_right,huv,mul_zero,sub_zero]
  calc
    _ = inner ℝ u (cgOperator (A-d • 1) v) := he.symm
    _ ≤ |inner ℝ u (cgOperator (A-d • 1) v)| := le_abs_self _
    _ ≤ ‖u‖*‖cgOperator (A-d • 1) v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖u‖*(‖cgOperator (A-d • 1)‖*‖v‖) :=
      mul_le_mul_of_nonneg_left ((cgOperator (A-d • 1)).le_opNorm v) (norm_nonneg u)
    _ = ‖A-d • 1‖ := by rw [hu,hv,mul_one,one_mul];rfl

end
end krylov.OneGradient
