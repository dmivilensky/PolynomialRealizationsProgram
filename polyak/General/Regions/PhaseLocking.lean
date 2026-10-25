import polyak.General.Regions.Radii
import polyak.General.Regions.Topology
import polyak.General.Regions.Periodic
import polyak.General.Regions.StrictTongue
import polyak.General.AngleComparison
import polyak.Threshold.Convergence

/-! Article: Theorem A. The convergence criterion acts on the original
nonlinear method in arbitrary real Hilbert spaces; closures are relative to
the actual admissible tuning domain. -/
namespace polyak.General.Regions
noncomputable section
open Dynamics Growth Filter Set
open scoped Topology

/-- The angle and cosine descriptions of the entire lag-one region coincide. -/
theorem omegaOne_iff_angle (q : Tuning) : OmegaOne q ↔
    ∀ ω∈Ioc (0:ℝ) Real.pi,ω/2<q.angle ω := by
  constructor
  · intro h ω hω
    exact (q.angle_gt_half_iff hω).mpr (h _ ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩)
  · intro h c hc
    by_cases hc1 : c=1
    · simpa only [hc1] using q.L_one_pos
    have hω : Real.arccos c∈Ioc (0:ℝ) Real.pi :=
      ⟨Real.arccos_pos.mpr (lt_of_le_of_ne hc.2 hc1),Real.arccos_le_pi c⟩
    have hh := (q.angle_gt_half_iff hω).mp (h _ hω)
    simpa only [Real.cos_arccos hc.1 hc.2] using hh

/-- The strict lag-one criterion controls the genuine free-pair envelope too. -/
theorem omegaOne_growth_lt_one (q : Tuning) (hq : OmegaOne q) :
    growthRate q.A q.B q.beta<1 := by
  have hh : growthRate q.A q.B q.beta<Real.exp 0 := by
    apply growthRate_lt_exp_of_certificates q.B_ne_zero
    intro t ht
    rcases ht.eq_or_lt with ht|ht
    · subst t
      apply Multipliers.lower_zero_certificate q {1} (fun _=>1) (by simp) (by simp)
      simpa [Multipliers.polynomial] using Multipliers.source_outer_positive q hq
    · apply Multipliers.lower_positive_certificate q {1} (fun _=>1) (by simp) (by simp) (by simp) ?_ ht
      simpa [Multipliers.polynomial] using Multipliers.source_outer_nonnegative q (fun c hc=>(hq c hc).le)
  simpa only [Real.exp_zero] using hh

/-- Theorem A(i), every actual run converges, including in infinite-dimensional Hilbert spaces. -/
theorem omegaOne_converges {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (q : Tuning) (hq : OmegaOne q)
    {f : E→ℝ} (hf : SmoothStronglyConvex q.x q.y f)
    (a : E) (hmin : ∀ y,f a≤f y) (x₀ : E) :
    Tendsto (iterate (gradient f) 1 q.beta x₀) atTop (𝓝 a) := by
  let r := growthRate q.A q.B q.beta
  let R := (r+1)/2
  have hrpos : 0<r := growthRate_pos _ _ _
  have hr1 : r<1 := omegaOne_growth_lt_one q hq
  have hRpos : 0<R := by dsimp [R]; linarith
  have hR1 : R<1 := by dsimp [R]; linarith
  have hrR : growthRate q.A q.B q.beta<R := by change r<R; dsimp [R]; linarith
  obtain ⟨C,_,hΓ⟩ := exists_envelope_le_mul_pow q.B_ne_zero hrR
  have hbound (n : ℕ) : ‖iterate (gradient f) 1 q.beta x₀ n-a‖≤
      (Real.sqrt 2*C*‖x₀-a‖)*R^n := by
    have hn := Threshold.original_norm_le_envelope hf a hmin 1 q.beta x₀ n
    rw [q.normalizedA_eq,q.normalizedB_eq] at hn
    have hm := mul_le_mul_of_nonneg_left (hΓ n) (Real.sqrt_nonneg 2)
    have hm' := mul_le_mul_of_nonneg_right hm (norm_nonneg (x₀-a))
    exact hn.trans (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hm')
  have hlim : Tendsto (fun n : ℕ=>(Real.sqrt 2*C*‖x₀-a‖)*R^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hRpos.le hR1).const_mul (Real.sqrt 2*C*‖x₀-a‖)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun _=>norm_nonneg _) hbound hlim)

/-- The weak upper bound on the entire relative closure, not only a parametrized boundary. -/
theorem closure_omegaOne_rate_le_one (q : Tuning)
    (hq : q∈closure {p : Tuning | OmegaOne p}) : q.rate≤1 :=
  Multipliers.source_rate_le_one q (closure_omegaOne_subset_weak hq)

/-- Theorem A(iii), exact rate at every rational phase-locked contact point. -/
theorem phase_locked_rate_eq_one (q : Tuning) {k : ℕ} (hk : 2<k)
    (hq : q∈closure {p : Tuning | OmegaOne p})
    (htouch : q.angle (rationalAngle 1 k)=Real.pi/k) : q.rate=1 := by
  exact le_antisymm (closure_omegaOne_rate_le_one q hq)
    (one_le_rate_of_rational_phase q (by simp) (by norm_num) (by omega) htouch.le)

end
end polyak.General.Regions
