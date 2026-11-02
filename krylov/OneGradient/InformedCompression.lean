import krylov.OneGradient.InformedScalarBound
import krylov.LinearAlgebra.Aggregation
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), true informed second-order operator bound.
Use: retain the full correlated hidden-pivot term of the actual known-base
leading output and bound it by the genuine original K_X(c) functional.
Source: proved sharp aggregate cross/compression and hidden-diagonal bounds,
orthogonal Pythagoras and the actual compact scalar maximum.
-/

namespace krylov.OneGradient
noncomputable section
open Finset krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace
variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The genuine informed second-order leading operator has the full
original sharp K_X(c) upper bound, with actual correlated increments,
known-base hidden diagonal and free output defect, including zero budgets.
Use: connect the original known-base leading expansion to its true
variational constant without separate triangle losses on the pivot.
Article: main_krylov, thm:local(b).
Proof: the genuine aggregate inequalities retain the actual correlation
between the cross vector, old compression and hidden diagonal. The cross
vector is orthogonal to the terminal unit direction; true Pythagoras
therefore gives the printed square root. Apply the genuine scalar maximum. -/
theorem informed_compression_bound (I : Finset ι) (K : ι → Submodule ℝ E)
    [∀ i,(K i).HasOrthogonalProjection] (T : ι → E →L[ℝ] E)
    (hT : ∀ i∈I,IsSelfAdjoint (T i)) (omega : ι → ℝ) (hbudget : ∀ i∈I,‖T i‖≤ omega i)
    (h : E) (hh : ∀ i∈I,h∈(K i)ᗮ) (hn : ‖h‖=1)
    (F : E →L[ℝ] E) (w c r : ℝ) (hF : ‖F‖≤ w) (hc : 0≤ c) (hr : |r|≤ c) :
    let X := ∑ i∈I,(K i).starProjection (T i h)
    let q := r+∑ i∈I,inner ℝ h (T i h)
    ‖(∑ i∈I,(K i).starProjection (T i ((K i).starProjection X)))+F (X+q • h)‖≤
      informedConstant (∑ i∈I,omega i) w c := by
  let X := ∑ i∈I,(K i).starProjection (T i h)
  let W := ∑ i∈I,omega i
  let q := r+∑ i∈I,inner ℝ h (T i h)
  have ha := aggregated_compression_action I K T hT omega hbudget h hh hn
  have hd := aggregated_hidden_diagonal I K T omega hbudget h hh hn
  have hW : 0≤ W := sum_nonneg (fun i hi => (norm_nonneg _).trans (hbudget i hi))
  have hw : 0≤ w := (norm_nonneg _).trans hF
  have hq : |q|≤ c+Real.sqrt (W^2-‖X‖^2) :=
    (abs_add_le r _).trans (add_le_add hr hd)
  have horth : inner ℝ X h=0 := by
    rw [sum_inner]
    apply sum_eq_zero
    intro i hi
    exact (Submodule.mem_orthogonal (K i) h).mp (hh i hi) _ ((K i).starProjection_apply_mem _)
  have hs : ‖X+q • h‖^2=‖X‖^2+q^2 := by
    rw [norm_add_sq_real,real_inner_smul_right,horth,mul_zero,mul_zero,add_zero,norm_smul,hn,mul_one,
      Real.norm_eq_abs,sq_abs]
  have hnorm : ‖X+q • h‖≤ Real.sqrt (‖X‖^2+(c+Real.sqrt (W^2-‖X‖^2))^2) := by
    apply (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr
    rw [hs]
    have hsq := (sq_le_sq₀ (abs_nonneg q) (by positivity : 0≤ c+Real.sqrt (W^2-‖X‖^2))).mpr hq
    rw [sq_abs] at hsq
    linarith
  have houtput : ‖F (X+q • h)‖≤ w*Real.sqrt (‖X‖^2+(c+Real.sqrt (W^2-‖X‖^2))^2) :=
    ((F.le_opNorm _).trans (mul_le_mul_of_nonneg_right hF (norm_nonneg _))).trans
      (mul_le_mul_of_nonneg_left hnorm hw)
  exact (norm_add_le _ _).trans ((add_le_add ha.2 houtput).trans
    (informed_scalar_bound hW hc (norm_nonneg X) ha.1))

end
end krylov.OneGradient
