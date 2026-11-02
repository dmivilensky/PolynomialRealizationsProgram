import krylov.Functions.CubicSelfConcordantBall

/-!
Article: main_krylov, prop:Fcycle(iii), explicit true-metric shrink margins.
Use: pay both the original varying quadratic and the true-minimizer metric
change by a linear tensor shrink, while preserving the printed SC radius.
Source: elementary power algebra; all inequalities retain their actual
nonnegative tensor and metric factors.
-/
namespace krylov.Functions
noncomputable section

/-- A linear shrink pays the actual base-Hessian drift at the true minimizer.
Article: main_krylov, prop:Fcycle(iii). -/
theorem shrink_true_metric_margin (a L M C p : ℝ)
    (ha : 0≤a) (hL : 0≤L) (hM : 0≤M) (hp : 0≤p)
    (hC : 2*a*(L+M)≤C) (hq : 0<1-C*p) :
    (1-C*p)^2≤1-(2*a*(1-C*p)^3)*p*L-(2*a*(1-C*p)^3)*(M*p) := by
  let q := 1-C*p
  have hC₀ : 0≤C := (by positivity : 0≤2*a*(L+M)).trans hC
  have hq₁ : q≤1 := by dsimp only [q]; nlinarith only [mul_nonneg hC₀ hp]
  have hq₀ : 0≤q := hq.le
  have hcube : q^3≤1 := by simpa only [one_pow] using pow_le_pow_left₀ hq₀ hq₁ 3
  have hsq : q^2≤q := by nlinarith only [mul_le_mul_of_nonneg_left hq₁ hq₀]
  have hs := mul_le_mul_of_nonneg_left hcube (by positivity : 0≤2*a*(L+M)*p)
  have hc := mul_le_mul_of_nonneg_right hC hp
  change q^2≤1-(2*a*q^3)*p*L-(2*a*q^3)*(M*p)
  dsimp only [q] at hsq
  dsimp only [q] at hs ⊢
  nlinarith only [hs,hsq,hc]

/-- The same genuine linear shrink preserves the complete printed
self-concordant radius in the true minimizer metric.
Article: main_krylov, prop:Fcycle(iii). -/
theorem shrink_sc_radius_margin (a L M C p R s : ℝ)
    (ha : 0≤a) (hL : 0≤L) (hM : 0≤M) (hp : 0≤p)
    (hC : 2*a*(L+M)≤C) (hq : 0<1-C*p) (hRdef : 2*a*R=1-s^2) :
    (s*(1-C*p))^2≤1-(2*a*(1-C*p)^3)*p*L-
      (2*a*(1-C*p)^3)*(R/(1-C*p)+M*p) := by
  let q := 1-C*p
  have hC₀ : 0≤C := (by positivity : 0≤2*a*(L+M)).trans hC
  have hq₁ : q≤1 := by dsimp only [q]; nlinarith only [mul_nonneg hC₀ hp]
  have hq₀ : 0≤q := hq.le
  have hcube : q^3≤1 := by simpa only [one_pow] using pow_le_pow_left₀ hq₀ hq₁ 3
  have hsq : q^2≤q := by nlinarith only [mul_le_mul_of_nonneg_left hq₁ hq₀]
  have hs₀ : 0≤2*a*(L+M)*p := by positivity
  have hbound := mul_le_mul_of_nonneg_left hcube hs₀
  have hc := mul_le_mul_of_nonneg_right hC hp
  have he : (2*a*q^3)*(R/q+M*p)=(2*a*R)*q^2+2*a*q^3*M*p := by
    have hne : q≠0 := hq.ne'
    field_simp [hne]
  change (s*q)^2≤1-(2*a*q^3)*p*L-(2*a*q^3)*(R/q+M*p)
  rw [he,hRdef]
  have hqp : q=1-C*p := rfl
  nlinarith only [hbound,hc,hsq,hqp]

end
end krylov.Functions
