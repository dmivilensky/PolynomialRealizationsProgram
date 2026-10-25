import polyak.FareyPlateau.LargeCurvature.PhaseGeometry
import polyak.FareyPlateau.LargeCurvature.Decomposition
import polyak.FareyPlateau.LargeCurvature.Taylor

noncomputable section
set_option maxHeartbeats 1200000
namespace polyak.FareyPlateau.LargeCurvature
open General Levels Set
open scoped BigOperators
namespace SourceData
variable {q : Tuning} {j k : ℕ} (B : SourceData q j k)

def mA : ℝ := B.a*sineMargin k/centralFactor k B.h

def centralCoefficient : ℝ :=
  -2*sineMargin k*B.mA/Real.pi+2*(∑ i,B.w i*deviation B.n₀ k B.bar i^2)+
    (4/3)*(∑ i,B.w i*|deviation B.n₀ k B.bar i|^3)*zoneRadius k B.N

theorem mA_pos : 0 < B.mA := by
  apply div_pos (mul_pos B.a_pos (sineMargin_pos B.kr))
  unfold centralFactor
  positivity

theorem centralCoefficient_neg : B.centralCoefficient < 0 :=
  central_coefficient_negative B.kr B.near B.N_ge (a1_faces B.large).2.2.2

theorem remainder_lower {x : ℝ} (hx : x ∈ Geometry.phaseBelow q 0) :
    B.mA/2*(x-B.ω)^2 ≤ tangentRemainder (ModeLocking.TwoLag.phase q 0) B.c B.bar B.ω x := by
  have hseg : uIcc B.ω x ⊆ Geometry.phaseBelow q 0 :=
    (Geometry.phaseBelow_convex q 0).ordConnected.uIcc_subset B.center_below hx
  have hf (y) (hy : y∈uIcc B.ω x) : ContDiffAt ℝ 2 (ModeLocking.TwoLag.phase q 0) y :=
    (ModeLocking.TwoLag.analyticAt_phase q 0 ⟨(hseg hy).1.1.le,(hseg hy).1.2.le⟩).contDiffAt
  apply tangent_quadratic_lower hf left_mem_uIcc right_mem_uIcc B.center_phase B.center_slope
  intro y hy
  simpa only [iteratedDeriv_eq_iterate,mA] using B.second_lower (hseg hy)

theorem window_delta {x : ℝ} (hx : x ∈ B.window) : |x-B.ω| ≤ zoneRadius k B.N := by
  exact abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩

theorem tangent_sine {x : ℝ} (hx : x ∈ B.window) :
    sineMargin k ≤ Real.sin (B.c+B.bar*(x-B.ω)/2) := by
  have hprod : |B.bar*(x-B.ω)| ≤ Real.pi/k := by
    rw [abs_mul]
    have hh := mul_le_mul B.bar_abs (B.window_delta hx) (abs_nonneg _) B.N_pos.le
    have he : B.N*zoneRadius k B.N=Real.pi/k := by unfold zoneRadius; field_simp [B.N_pos.ne']
    rwa [he] at hh
  have hp := abs_le.mp hprod
  apply sin_lower_on_trimmed_interval (show 0 ≤ Real.pi/(2*k) by positivity)
    (show Real.pi/(2*k) ≤ Real.pi/2 by
      exact div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) (by have := B.kr; linarith))
  have hhalf : 3*(Real.pi/k)/2 ≤ Real.pi-Real.pi/(2*k) := by
    have he : 3*(Real.pi/k)/2+Real.pi/(2*k)=2*Real.pi/k := by ring
    have hsmall : 2*Real.pi/k ≤ Real.pi := by
      apply (div_le_iff₀ B.kp).mpr
      nlinarith [B.kr,Real.pi_pos]
    linarith
  have he : Real.pi/(2*k)=(Real.pi/k)/2 := by ring
  dsimp only [c]
  rw [he]
  constructor <;> linarith

theorem central_symbol_bound_actual {x : ℝ} (hx : x ∈ Geometry.phaseBelow q 0) :
    indexedSymbol q 0 B.n B.w x ≤ (x-B.ω)^2*B.centralCoefficient := by
  let δ := x-B.ω
  let ℓ := B.c+B.bar*δ/2
  let g := ModeLocking.TwoLag.phase q 0 x-ℓ
  have hw := fun i=>(B.positive i).le
  have hd := B.window_delta (B.below_in_window hx)
  have hlower := B.remainder_lower hx
  have hg0 : 0 ≤ g := by
    have hm : 0 ≤ B.mA/2*(x-B.ω)^2 := by positivity [B.mA_pos]
    exact hm.trans hlower
  have hℓp : 0 < ℓ := by
    have hh := middle_zone_angles B.kr B.N_pos B.bar_abs hd
    exact hh.1
  have hgp : g ≤ Real.pi/2 := by
    have hθ := hx.2
    rw [←B.phase_eq ⟨hx.1.1.le,hx.1.2.le⟩] at hθ
    dsimp [g]
    linarith
  have hdecomp := central_decomposition B.n B.w B.normalization (δ := δ)
    (θ := ModeLocking.TwoLag.phase q 0 x) (bar := B.bar) B.lag_phase
  have hext : indexedSymbol q 0 B.n B.w x =
      ∑ i,B.w i*Geometry.extendedLag (fun _=>ModeLocking.TwoLag.phase q 0 x) (B.n i) (B.ω+δ) := by
    unfold indexedSymbol
    have he : B.ω+δ=x := by dsimp [δ]; ring
    rw [he]
    simp only [ModeLocking.lagExtension,Geometry.extendedLag,ModeLocking.TwoLag.phase]
  rw [hext,hdecomp]
  have hmean := deviation_mean B.kp.ne' (n := (B.n₀:ℝ)) (s := B.bar)
  have hh := central_symbol_bound B.w (deviation B.n₀ k B.bar) hw B.normalization hmean
    (sineMargin_pos B.kr).le (B.tangent_sine (B.below_in_window hx)) ⟨hg0,hgp⟩ hlower hd
  simpa only [deviation,n,integerLag_cast,Int.cast_natCast,δ,ℓ,g,centralCoefficient] using hh

end SourceData
end polyak.FareyPlateau.LargeCurvature
