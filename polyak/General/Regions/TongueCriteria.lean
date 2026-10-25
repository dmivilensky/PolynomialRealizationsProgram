import polyak.General.Regions.Explicit
import polyak.General.Regions.SingleFeasible
import polyak.General.AngleComparison

/-! Article: Corollary C(b). Rational tongues and fractional lag-one regions
are exact inequalities, with the phase-locked j=1 comparison as a special case. -/
namespace polyak.General.Regions
noncomputable section

/-- Angle thresholds below pi are equivalent to cotangent thresholds with correct orientation. -/
theorem angle_le_iff_Xi (q : Tuning) {ω φ : ℝ}
    (hω : ω∈Set.Ioo 0 Real.pi) (hφ : φ∈Set.Ioo 0 Real.pi) :
    q.angle ω≤φ ↔ (Real.cos φ/Real.sin φ)*Real.sin ω≤q.Xi (Real.cos ω) := by
  have hs : 0<Real.sin ω := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have he := cot_strictAnti (q.angle_mem hω) hφ
  have hle : q.angle ω≤φ ↔ Real.cos φ/Real.sin φ≤Real.cos (q.angle ω)/Real.sin (q.angle ω) := by
    rw [← not_lt,← not_lt,he]
  rw [hle,q.cot_angle hω,le_div_iff₀ hs]

/-- Corollary C(b), the two exact tests for every primitive root-of-unity tongue. -/
theorem rational_angle_le_iff_explicit (q : Tuning) {j k : ℕ}
    (hj : 1≤j) (hjk : 2*j<k) :
    let ω := rationalAngle j k
    let h := (Real.cos (Real.pi/k)/Real.sin (Real.pi/k))*Real.sin ω
    (q.angle ω≤Real.pi/k ↔ h≤q.Xi (Real.cos ω)) ∧
      (h≤q.Xi (Real.cos ω) ↔ q.L (Real.cos ω)≤
        (q.y-q.x)*(1-q.beta)*(1+Real.cos ω-h)) := by
  dsimp only
  have hk : (1:ℝ)<k := by exact_mod_cast (show 1<k by omega)
  refine ⟨angle_le_iff_Xi q (rationalAngle_mem hj hjk) ?_,Xi_ge_iff_L_le q _ _⟩
  exact ⟨div_pos Real.pi_pos (by linarith),div_lt_self Real.pi_pos hk⟩

/-- In the j=1 tongue the right-hand side is exactly zero. -/
theorem first_tongue_iff_L_nonpos (q : Tuning) {k : ℕ} (hk : 2<k) :
    q.angle (rationalAngle 1 k)≤Real.pi/k ↔ q.L (Real.cos (rationalAngle 1 k))≤0 := by
  have hω := rationalAngle_mem (j:=1) (by norm_num) (by omega : 2*1<k)
  have hhalf : rationalAngle 1 k/2=Real.pi/k := by dsimp [rationalAngle]; ring
  have he := cot_half hω
  rw [hhalf] at he
  have hs : Real.sin (rationalAngle 1 k)≠0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2)
  have hmul : (Real.cos (Real.pi/k)/Real.sin (Real.pi/k))*Real.sin (rationalAngle 1 k)=
      1+Real.cos (rationalAngle 1 k) := by rw [he]; exact div_mul_cancel₀ _ hs
  exact (rational_angle_le_iff_explicit q (j:=1) (by norm_num) (by omega)).1.trans
    (by rw [hmul]; exact Xi_ge_one_add_iff_L_nonpos q _)

end
end polyak.General.Regions
