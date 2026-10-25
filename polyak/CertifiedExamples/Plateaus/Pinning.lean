import polyak.Levels.Program.ChebyshevLag
import polyak.Levels.Program.Pinning
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The finite polynomial pinning determinant is the actual sine determinant
times nonzero row factors. The equality retains signed lags and canonical
residue representatives on every support grid. -/
noncomputable section
namespace polyak.CertifiedExamples.Plateaus
open General Levels Spectral

theorem pinning_sine_polynomial (q : Tuning) (n : ℤ) (hn : n≠0)
    (ω : Levels.Frequency) (hω : 0<(ω:ℝ) ∧ (ω:ℝ)<Real.pi) :
    Real.sin ((n:ℝ)*(ω:ℝ)-q.angle ω)=Real.sin (q.angle ω)*
      ((n.sign:ℝ)*q.Xi (Real.cos (ω:ℝ))*chebU (n.natAbs-1) (Real.cos (ω:ℝ))-
        chebT n.natAbs (Real.cos (ω:ℝ))) := by
  have hs : Real.sin (ω:ℝ)≠0 := (Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2).ne'
  have hθ : Real.sin (q.angle ω)≠0 :=
    (Real.sin_pos_of_pos_of_lt_pi (q.angle_mem hω).1 (q.angle_mem hω).2).ne'
  have hc : Real.cos (q.angle ω)=Real.sin (q.angle ω)*
      (q.Xi (Real.cos (ω:ℝ))/Real.sin (ω:ℝ)) := by
    exact (div_eq_iff hθ).mp (q.cot_angle hω) |>.trans (mul_comm _ _)
  have hk : 1≤n.natAbs := by have := Int.natAbs_pos.mpr hn; omega
  have hsin : chebU (n.natAbs-1) (Real.cos (ω:ℝ))*Real.sin (ω:ℝ)=
      Real.sin ((n.natAbs:ℝ)*(ω:ℝ)) := by
    have h := chebU_sin (n.natAbs-1) (ω:ℝ)
    have he : ((n.natAbs-1:ℕ):ℝ)+1=n.natAbs := by exact_mod_cast Nat.sub_add_cancel hk
    rwa [he] at h
  rw [Real.sin_sub,hc,cos_int_mul_natAbs,←chebT_cos,sin_int_mul_natAbs,←hsin]
  field_simp

theorem sin_lag_mod_grid {L : ℕ} {ω : Levels.Frequency} (hω : ω∈periodicGrid L)
    (n : ℤ) (θ : ℝ) :
    Real.sin ((n:ℝ)*(ω:ℝ)-θ)=Real.sin (((n%(L:ℤ):ℤ):ℝ)*(ω:ℝ)-θ) := by
  have he : n=n%L+(n/L)*L := (Int.emod_add_ediv_mul n L).symm
  conv_lhs => rw [he]
  exact sin_lag_add_mul_grid hω (n%L) (n/L) θ

theorem pinning_det_of_polynomial {L d : ℕ} (q : Tuning) (u : Fin d→Levels.Frequency)
    (hu : ∀i,0<(u i:ℝ) ∧ (u i:ℝ)<Real.pi)
    (hg : ∀i,u i∈periodicGrid L) (base reps : Fin d→ℤ)
    (hb : ∀i,base i≠0) (hm : ∀i,base i%(L:ℤ)=reps i)
    (hdet : Matrix.det (fun i r : Fin d=>(L:ℝ)*
      (chebT (base r).natAbs (Real.cos (u i:ℝ))-
        ((base r).sign:ℝ)*q.Xi (Real.cos (u i:ℝ))*
          chebU ((base r).natAbs-1) (Real.cos (u i:ℝ))))≠0) :
    Matrix.det (fun i r : Fin d=>Real.sin ((reps r:ℝ)*(u i:ℝ)-q.angle (u i)))≠0 := by
  classical
  let M : Matrix (Fin d) (Fin d) ℝ := fun i r=>Real.sin ((reps r:ℝ)*(u i:ℝ)-q.angle (u i))
  let D : Matrix (Fin d) (Fin d) ℝ := Matrix.diagonal (fun i=>-(L:ℝ)/Real.sin (q.angle (u i)))
  have he : (fun i r : Fin d=>(L:ℝ)*
      (chebT (base r).natAbs (Real.cos (u i:ℝ))-
        ((base r).sign:ℝ)*q.Xi (Real.cos (u i:ℝ))*
          chebU ((base r).natAbs-1) (Real.cos (u i:ℝ))))=D*M := by
    ext i r
    rw [Matrix.diagonal_mul]
    change _=(-(L:ℝ)/Real.sin (q.angle (u i)))*
      Real.sin ((reps r:ℝ)*(u i:ℝ)-q.angle (u i))
    rw [←hm r,←sin_lag_mod_grid (hg i) (base r),pinning_sine_polynomial q _ (hb r) _ (hu i)]
    have hθ : Real.sin (q.angle (u i))≠0 :=
      (Real.sin_pos_of_pos_of_lt_pi (q.angle_mem (hu i)).1 (q.angle_mem (hu i)).2).ne'
    field_simp
    ring
  rw [he,Matrix.det_mul] at hdet
  exact (mul_ne_zero_iff.mp hdet).2

end polyak.CertifiedExamples.Plateaus
