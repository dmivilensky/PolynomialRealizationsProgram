import krylov.Secant.NormalizedModel
import krylov.Stability.ContDiffSpectralMatrix
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), genuine native basis-change model order.
Use: real S/D observed basis changes preserve the latest model to first
order at a genuine conjugate reference with actual diagonal column scales.
Source: exact latest-information selector, proved diagonal congruence
invariance and reused genuine finite spectral matrix congruence remainders.
-/

namespace krylov.Secant
noncomputable section
open Matrix Filter Topology Asymptotics krylov.LinearAlgebra
open scoped Matrix.Norms.L2Operator
variable {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Latest-information selection preserves an actual matrix difference.
Use: true observed model differences retain exactly their source order.
Article: main_krylov, thm:local(a), exact latest selector linearity.
Proof: the true selector reads the same pair of finite coordinates. -/
theorem latest_sub (C D : Matrix (Fin n) (Fin n) ℝ) : latest (C-D)=latest C-latest D := rfl

/-- The real latest-information selector preserves every true spectral
matrix big-O order through its genuine finite coordinate equivalence.
Use: model-order comparisons keep the original spectral matrix norm.
Article: main_krylov, thm:local(a), true latest model remainder transfer.
Proof: each selected matrix entry is exactly a fixed genuine input entry;
reuse the existing spectral/finite-coordinate asymptotic dictionary. -/
theorem latest_bigO {alpha : Type*} {l : Filter alpha}
    (C : alpha → Matrix (Fin n) (Fin n) ℝ) (s : alpha → ℝ) (hC : C =O[l] s) :
    (fun z => latest (C z)) =O[l] s :=
  (matrix_bigO_iff_entry _ _).mpr (fun i j => (matrix_bigO_iff_entry C s).mp hC (min i j) (max i j))

/-- An arbitrary true symmetric reference pairing form contributes no
latest-information congruence defect, even for a nonconjugate moving basis.
Use: only the actual vanishing observed drift enters basis-change errors.
Article: main_krylov, thm:local(a), genuine model congruence defect shift.
Proof: a real congruence of the true symmetric reference is symmetric, so
the actual latest selector fixes it exactly. Distribute the same actual
reference difference on both sides and cancel its exact congruence. -/
theorem latest_congruence_symmetric_shift (C C0 T : Matrix (Fin n) (Fin n) ℝ) (hC0 : C0.IsSymm) :
    latest (Tᵀ*C*T)-Tᵀ*latest C*T=
      latest (Tᵀ*(C-C0)*T)-Tᵀ*latest (C-C0)*T := by
  have hs : (Tᵀ*C0*T).IsSymm := by
    simp only [Matrix.IsSymm,Matrix.transpose_mul,Matrix.transpose_transpose,hC0.eq,Matrix.mul_assoc]
  have he : Tᵀ*(C-C0)*T=Tᵀ*C*T-Tᵀ*C0*T := by noncomm_ring
  rw [he,latest_sub,latest_eq_of_isSymm hs,latest_sub,latest_eq_of_isSymm hC0]
  simp only [Matrix.mul_sub,Matrix.sub_mul]
  abel

/-- The genuine latest model commutes with actual C-one observed basis
changes up to quadratic order when the true reference pairing is symmetric
and the real reference basis change is diagonal. No model-error estimate
is supplied as a premise, and the moving basis need not remain diagonal.
Use: derive the actual informed S/D virtual-quotient first-order dictionary.
Article: main_krylov, thm:local(a), genuine native model congruence order.
Proof: subtract the true symmetric reference pairing, which has exactly
zero defect. Genuine C-one changes and drift are first order. Apply the
existing matrix congruence freezing theorem twice, before and after the
actual latest selector. Its exact diagonal congruence identity cancels
their true reference terms, leaving a genuine quadratic model difference. -/
theorem latest_congruence_quadratic (C T : X → Matrix (Fin n) (Fin n) ℝ)
    (hC : ContDiffAt ℝ 1 C 0) (hT : ContDiffAt ℝ 1 T 0)
    (hC0 : (C 0).IsSymm) (d : Fin n → ℝ) (hT0 : T 0=diagonal d) :
    (fun z => latest ((T z)ᵀ*C z*T z)-(T z)ᵀ*latest (C z)*T z)
      =O[𝓝 0] (fun z => ‖z‖^2) := by
  let H := fun z => C z-C 0
  have hH : H =O[𝓝 0] (fun z => ‖z‖) := by
    simpa only [sub_zero] using (hC.differentiableAt (by norm_num)).isBigO_sub.norm_right
  have hTd : (fun z => T z-diagonal d) =O[𝓝 0] (fun z => ‖z‖) := by
    simpa only [hT0,sub_zero] using (hT.differentiableAt (by norm_num)).isBigO_sub.norm_right
  have hs : Tendsto (fun z : X => ‖z‖) (𝓝 0) (𝓝 0) := by simpa only [norm_zero] using continuous_norm.continuousAt.tendsto (x := (0 : X))
  have hleft := latest_bigO _ _ (matrix_congruence_first_order T H (diagonal d) _ hs hTd hH)
  have hright := matrix_congruence_first_order T (fun z => latest (H z)) (diagonal d) _ hs hTd (latest_bigO H _ hH)
  apply (hleft.sub hright).congr_left
  intro z
  have hshift : latest ((T z)ᵀ*C z*T z)-(T z)ᵀ*latest (C z)*T z=
      latest ((T z)ᵀ*H z*T z)-(T z)ᵀ*latest (H z)*T z :=
    latest_congruence_symmetric_shift (C z) (C 0) (T z) hC0
  rw [hshift]
  simp only [latest_sub,Matrix.diagonal_transpose,latest_diagonal_congruence]
  abel

end
end krylov.Secant
