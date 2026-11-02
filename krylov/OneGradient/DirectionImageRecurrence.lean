import krylov.OneGradient.DirectionImageJet
set_option autoImplicit false
/-!
Article: main_krylov, thm:I, actual one-step direction image-error first jets.
Use: recover the source's genuine scalar replay recurrence from the
proved native differentiated recursion and real sparse reference weights.
Source: actual primitive query/coefficient calculus, true reference trial
domains and the derived newest-coordinate native virtual solve.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Stability
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The original initial observed direction image has zero true error first jet.
Use: initialize the actual direction-basis response recurrence.
Article: main_krylov, thm:I, iota_0'=0.
Proof: the actual differentiated native recursion has an empty previous
window, and its genuine nonzero reference trial cancels. -/
theorem xrfcD_image_error_zero_jet
    (trial : History E → ℝ) (A : ℝ → ℕ → E →L[ℝ] E)
    (hA : ∀ i,ContDiffAt ℝ 1 (fun t => A t i) 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=fun _ => Q) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (N : ℕ) (hN : 0<N)
    (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (hT : ∀ k<N,ContDiffAt ℝ 1 (trialCoordinate trial k)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _ => Q) g k)) :
    deriv (fun t => xrfcDImageError trial (A t) g 0) 0=0 := by
  have h := xrfcD_image_error_first_jet trial A hA Q hA0 hQ hpos g N hpre ht hT 0 hN
  have hz : trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g 0) •
      deriv (fun t => xrfcDImageError trial (A t) g 0) 0=0 := by simpa only [Finset.univ_eq_empty,Finset.sum_empty] using h
  exact (smul_eq_zero.mp hz).resolve_left (ht 0 hN)

/-- The actual original direction replay has exactly the printed one-step
image-error derivative recurrence on arbitrary primitive C1 operator paths.
Use: its finite unrolling yields the original amplitude sum with no oblique flags.
Article: main_krylov, thm:I, iota_(k+1)'=(rho_k/tau_(k+1)) (DeltaA_k d_k^0-iota_k').
Proof: insert the genuinely computed sparse reference coefficient vector in
the actual differentiated native recursion, retain only its newest coordinate
and cancel the actual nonzero reference trial. -/
theorem xrfcD_image_error_successor_jet
    (trial : History E → ℝ) (A : ℝ → ℕ → E →L[ℝ] E)
    (hA : ∀ i,ContDiffAt ℝ 1 (fun t => A t i) 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=fun _ => Q) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E,v≠0 → 0 < inner ℝ v (Q v)) (g : E) (N : ℕ)
    (hpre : ∀ i<N,CG.gradient Q g i≠0)
    (ht : ∀ i<N,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g i)≠0)
    (hT : ∀ k<N,ContDiffAt ℝ 1 (trialCoordinate trial k)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _ => Q) g k))
    (k : ℕ) (hk : k+1<N) :
    deriv (fun t => xrfcDImageError trial (A t) g (k+1)) 0=
      ((CG.length Q g k-trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g k))/
        trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g (k+1))) •
        ((deriv (fun t => A t (k+1)) 0-deriv (fun t => A t k) 0) (CG.direction Q g k)-
          deriv (fun t => xrfcDImageError trial (A t) g k) 0) := by
  have h := xrfcD_image_error_first_jet trial A hA Q hA0 hQ hpos g N hpre ht hT (k+1) hk
  rw [xrfcD_reference_coefficients trial Q hQ hpos g N hpre ht k (by omega)] at h
  simp only [ite_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    Fin.val_zero,Nat.add_sub_cancel,Nat.sub_zero] at h
  have hh := congrArg (fun v =>
    (trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => Q) g (k+1)))⁻¹ • v) h
  simp only [smul_smul,inv_mul_cancel₀ (ht (k+1) hk),one_smul] at hh
  rw [div_eq_mul_inv,mul_comm]
  exact hh

end
end krylov.OneGradient
