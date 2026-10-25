import polyak.FareyPlateau.FanAnalysis.DualJets
import polyak.FareyPlateau.FanAnalysis.OriginJets
import polyak.FareyPlateau.FanAnalysis.DualSeparation
import polyak.FareyPlateau.FanAnalysis.GridAccess

/-! The actual finite dual separating every nonzero pair of nonnegative masses
above the critical quadratic shift. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis.Actual
open General Levels ModeLocking Filter Set
open scoped Topology
variable {q : Tuning} {j k : ℕ} (A : Edge.AdjacentData q j k)

def pairLag (P : Fan.Data) (e δ wa wc : ℝ) (n : ℤ) : ℝ :=
  wa*(Real.cos (nearAngle A e δ)-Real.cos ((n : ℝ)*P.near-nearAngle A e δ))+
  wc*(Real.cos (farAngle A e δ)-Real.cos ((n : ℝ)*P.far-farAngle A e δ))

theorem origin_constraint (P : Fan.Data) (hk : P.k=k) {e δ wa wc : ℝ}
    (hδ : P.delta=δ) (hfeas : ∀n : ℤ, 0 ≤ pairLag A P e δ wa wc n) (r : ℤ) :
    0 ≤ wa*lagPath 0 ((r : ℝ)*k) (nearAngle A e) δ+
      wc*lagPath 0 (-((k : ℝ)-1)*((r : ℝ)*k)) (farAngle A e) δ := by
  obtain ⟨n,l,hn⟩ := P.access_origin r
  rw [hk, hδ] at hn
  push_cast at hn
  have hh := hfeas n
  unfold pairLag at hh
  rw [companion_cosine P n (farAngle A e δ), hk] at hh
  push_cast at hh
  have hnear : Real.cos ((n : ℝ)*P.near-nearAngle A e δ)=
      Real.cos (((r : ℝ)*k)*δ-nearAngle A e δ) := by
    rw [hn]
    convert Real.cos_add_int_mul_two_pi (((r : ℝ)*k)*δ-nearAngle A e δ) l using 1; congr 1; ring
  have hfar : Real.cos (((k : ℝ)-1)*((n : ℝ)*P.near)+farAngle A e δ)=
      Real.cos (-((k : ℝ)-1)*((r : ℝ)*k)*δ-farAngle A e δ) := by
    rw [hn]
    rw [show -((k : ℝ)-1)*((r : ℝ)*k)*δ-farAngle A e δ =
      -(((k : ℝ)-1)*((r : ℝ)*k)*δ+farAngle A e δ) by ring, Real.cos_neg]
    convert Real.cos_add_int_mul_two_pi
      (((k : ℝ)-1)*((r : ℝ)*k)*δ+farAngle A e δ) (((k : ℤ)-1)*l) using 1
    push_cast
    congr 1
    ring
  rw [hnear, hfar] at hh
  simpa only [lagPath, zero_add] using hh

theorem dual_constraint (P : Fan.Data) (hj : P.j=j) (hk : P.k=k) {e δ wa wc : ℝ}
    (hδ : P.delta=δ) (hfeas : ∀n : ℤ, 0 ≤ pairLag A P e δ wa wc n) :
    0 ≤ wa*dualPath A (nearAngle A e) 1 δ+
      wc*dualPath A (farAngle A e) (-((k : ℝ)-1)) δ := by
  have hcenter : P.center=(A.frequency : ℝ) := by
    change 2*Real.pi*P.j/P.k=2*Real.pi*j/k
    rw [hj,hk]
    push_cast
    rfl
  have hnear : P.near=(A.frequency : ℝ)+δ := by
    have hh := P.near_displacement
    rw [hcenter,hδ] at hh
    linarith
  have hfar : P.far=(A.frequency : ℝ)-((k : ℝ)-1)*δ := by
    have hh := P.far_displacement
    rw [hcenter,hδ,hk] at hh
    push_cast at hh
    exact hh
  have h₁ := mul_nonneg (sub_nonneg.mpr A.mix_lt.le) (hfeas A.lower)
  have h₂ := mul_nonneg A.mix_pos.le (hfeas A.upper)
  have he : wa*dualPath A (nearAngle A e) 1 δ+wc*dualPath A (farAngle A e) (-((k : ℝ)-1)) δ=
      (1-A.mix)*pairLag A P e δ wa wc A.lower+A.mix*pairLag A P e δ wa wc A.upper := by
    unfold dualPath lagPath pairLag
    rw [hnear,hfar]
    ring_nf
  rw [he]
  exact add_nonneg h₁ h₂

theorem fan_infeasible_small {e : ℝ} (he : critical A < e) :
    ∀ᶠ δ in 𝓝[≠] 0, ∀P : Fan.Data, P.j=j → P.k=k → P.delta=δ →
      ∀wa wc : ℝ, 0 ≤ wa → 0 ≤ wc → 0 < wa+wc → ¬∀n : ℤ, 0 ≤ pairLag A P e δ wa wc n := by
  have hm : (0 : ℝ)<(k : ℝ)-1 := by
    have hkR : (3 : ℝ) ≤ k := by exact_mod_cast A.period_ge
    linarith
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast A.period_ge
  have hkpos : (0 : ℝ)<k := by linarith
  have hsin := sin_positive A
  have ht : 0 < (k : ℝ)*Real.sin (Real.pi/k) := mul_pos hkpos hsin
  have hn : ((k : ℝ)-1)*(-deriv^[2] A.function A.frequency-2*e*(Real.sin (Real.pi/k))^3)+
      (-((k : ℝ)-1)^2*deriv^[2] A.function A.frequency-2*e*(Real.sin (Real.pi/k))^3)<0 := by
    have hs : (0 : ℝ)<2*(Real.sin (Real.pi/k))^3 := by positivity
    unfold critical at he
    have hh := (div_lt_iff₀ hs).mp he
    nlinarith [mul_neg_of_pos_of_neg hkpos (show -((k : ℝ)-1)*deriv^[2] A.function A.frequency-2*e*(Real.sin (Real.pi/k))^3<0 by linarith)]
  have hp₁ := near_origin_limit A e (k : ℝ)
  have hp₂ := far_origin_limit A e (-((k : ℝ)-1)*k)
  have hm₁ := near_origin_limit A e (-(k : ℝ))
  have hm₂ := far_origin_limit A e (((k : ℝ)-1)*k)
  have hsep := eventual_two_atom_separation hm ht hn (near_dual_limit A e) (far_dual_limit A e)
    (by convert hp₁ using 1; congr 1; ring)
    (by convert hp₂ using 1; congr 1; ring)
    (by convert hm₁ using 1; congr 1; ring)
    (by convert hm₂ using 1; congr 1; ring)
  filter_upwards [hsep] with δ hδ P hj hk hPd wa wc hwa hwc hwn hfeas
  apply hδ wa wc hwa hwc hwn
  refine ⟨dual_constraint A P hj hk hPd hfeas, ?_, ?_⟩
  · simpa only [Int.cast_one, one_mul] using origin_constraint A P hk hPd hfeas 1
  · simpa only [Int.cast_neg, Int.cast_one, neg_one_mul, mul_neg, neg_neg, neg_mul, one_mul] using origin_constraint A P hk hPd hfeas (-1)

end polyak.FareyPlateau.FanAnalysis.Actual
