import krylov.OneGradient.InformedCanonicalRows
import krylov.LinearAlgebra.FullFrameOrder
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine full native incoming vector.
Use: reconstruct the actual full-cycle S/D incoming gradient from its
true canonical coordinates, retaining actual increments and trial error.
Source: genuine complete full-atom CG frame, actual native row derivation
and exact finite orthonormal reconstruction in the original physical norm.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology Asymptotics krylov.Methods krylov.Reference krylov.Secant krylov.LinearAlgebra
open scoped InnerProductSpace BigOperators
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The genuine canonical incoming drift vector, in the known reference's
true full CG frame. Each coefficient retains the actual whole segment
drift from its true old query to the last evaluated segment. The final
coefficient is exactly zero because that actual difference is zero.
Use: the source fhat is reconstructed from real observed-segment changes,
without substituting operator derivatives or a hypothetical response field.
Article: main_krylov, thm:local(a), actual incoming fhat. -/
def informedIncomingDrift (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (n+1)))
    (A : ℕ → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))) :
    EuclideanSpace ℝ (Fin (n+1)) :=
  let R := cgOperator (metricRoot base)⁻¹
  ∑ i : Fin (n+1),inner ℝ (canonicalCGUnitStep base g i.val)
    ((R*(A n-A i.val)*R) (canonicalCGUnitStep base g n)) • canonicalCGUnitStep base g i.val

/-- The true full-cycle informed S/D incoming gradient has the original
explicit drift-minus-last-pivot vector coefficient with a quadratic
full-parameter remainder. Every physical difference and true native
relative trial error is retained, and the complete real vector is proved.
Use: substitute this actual incoming coefficient into the already proved
genuine cubic native output formulas in either implemented basis.
Article: main_krylov, thm:local(a), actual full incoming vector formula.
Proof: actual native program/regularity/reference dictionaries derive
the true canonical old and last rows. The genuine full-atom CG frame is
orthonormal and complete. Its exact finite coordinate synthesis gives the
actual drift vector; the last drift coefficient vanishes identically.
Reconstruct the full vector remainder from all genuine coordinate bounds. -/
theorem informed_native_incoming_vector (directions : Bool)
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hc : referenceAtomCount base hb g=n+1)
    (A : X → ℕ → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (hA : ∀ j,ContDiffAt ℝ 1 (fun z => A z j) 0) (hA0 : A 0=fun _ => cgOperator base)
    (hsym : ∀ z j,(A z j).toLinearMap.IsSymmetric) :
    let trial := informedTrial (cgOperator base)
    let m := xrfcBasisMethod directions trial
    let R := cgOperator (metricRoot base)⁻¹
    let sigma := ‖canonicalCGStep base g n‖
    let h := canonicalCGUnitStep base g n
    (fun z => R (oneGradientGradient m (A z) g (n+1))-
      sigma • (informedIncomingDrift base g (A z)-xrfcNativeTrialError directions trial (A z) g n • h))
        =O[𝓝 0] (fun z => ‖z‖^2) := by
  let trial := informedTrial (cgOperator base)
  let m := xrfcBasisMethod directions trial
  let R := cgOperator (metricRoot base)⁻¹
  let sigma := ‖canonicalCGStep base g n‖
  let q := fun i : Fin (n+1) => canonicalCGUnitStep base g i.val
  let F := fun z => informedIncomingDrift base g (A z)
  let eps := fun z => xrfcNativeTrialError directions trial (A z) g n
  let G := fun z => oneGradientGradient m (A z) g (n+1)
  let error := fun z => R (G z)-sigma • (F z-eps z • q (Fin.last n))
  have ho : Orthonormal ℝ q := canonicalCG_frame_of_full_atoms base hb g hc
  have hrows := informed_native_canonical_rows directions base hb g hc A hA hA0 hsym
  have hF (z : X) (i : Fin (n+1)) : inner ℝ (q i) (F z)=
      inner ℝ (q i) ((R*(A z n-A z i.val)*R) (q (Fin.last n))) :=
    ho.inner_right_fintype (fun j => inner ℝ (q j) ((R*(A z n-A z j.val)*R) (q (Fin.last n)))) i
  have hFLast (z : X) : inner ℝ (q (Fin.last n)) (F z)=0 := by
    rw [hF]
    simp only [Fin.val_last,sub_self,mul_zero,zero_mul,_root_.zero_apply,inner_zero_right]
  apply full_orthonormal_frame_order q ho error (fun z => ‖z‖^2)
  intro i
  by_cases hi : i.val<n
  · let j : Fin n := ⟨n-1-i.val,by omega⟩
    have hage : n-1-j.val=i.val := by dsimp only [j];omega
    have hne : i≠Fin.last n := by intro he;have hv := congrArg Fin.val he;rw [Fin.val_last] at hv;omega
    have horth : inner ℝ (q i) (q (Fin.last n))=0 := ho.inner_eq_zero (i := i) (j := Fin.last n) hne
    have hr : (fun z => inner ℝ (q i) (R (G z))-
        sigma*inner ℝ (q i) ((R*(A z n-A z i.val)*R) (q (Fin.last n)))) =O[𝓝 0] (fun z => ‖z‖^2) := by
      simpa only [hage,q,R,G,m,trial,sigma,Fin.val_last] using hrows.1 j
    apply hr.congr_left
    intro z
    change _=inner ℝ (q i) (R (G z)-sigma • (F z-eps z • q (Fin.last n)))
    rw [inner_sub_right,real_inner_smul_right,inner_sub_right,real_inner_smul_right,hF,horth,mul_zero,sub_zero]
  · have he : i=Fin.last n := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    subst i
    have hself : inner ℝ (q (Fin.last n)) (q (Fin.last n))=1 := by
      rw [real_inner_self_eq_norm_sq,ho.norm_eq_one (Fin.last n),one_pow]
    apply hrows.2.congr_left
    intro z
    change _=inner ℝ (q (Fin.last n)) (R (G z)-sigma • (F z-eps z • q (Fin.last n)))
    rw [inner_sub_right,real_inner_smul_right,inner_sub_right,real_inner_smul_right,hFLast,hself,
      mul_one,zero_sub,mul_neg,sub_neg_eq_add]
    rfl

end
end krylov.OneGradient
