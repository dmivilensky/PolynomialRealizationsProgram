import nesterov.Spread.PhaseAverages
import nesterov.Spread.LagBounds

/-! Every noncritical lag has a strict margin for the actual smooth profile. -/
namespace nesterov.Spread
noncomputable section
open MeasureTheory Spectral Set

theorem band_endpoints {K : ℕ} (hK : 3≤K) {s : ℝ} (_hs : 0<s)
    (hs1 : s≤canonicalKernel.s1) :
    0≤centerAngle K-s*centerAngle K ∧ centerAngle K+s*centerAngle K≤Real.pi := by
  have hω := centerAngle_pos hK
  have hωu := centerAngle_le hK
  have hs6 := hs1.trans canonicalKernel.s1_le_one_sixth
  have hh := mul_le_mul hs6 hωu hω.le (by norm_num : (0:ℝ)≤1/6)
  constructor <;> nlinarith [Real.pi_pos]

theorem ideal_upper_decay (D : KernelData) {K n : ℕ} {s t m : ℝ}
    (hω : 0<centerAngle K) (hs : 0<s) (ht : t<0) (hm : 0<m)
    (hlarge : m/4<(n:ℝ)*|t|) :
    Real.cos (((n:ℝ)+1/2)*centerAngle K)*D.hat (((n:ℝ)+1/2)*(s*centerAngle K))≤
      D.longConstant*(|t|/(m*(s*centerAngle K)))^2 := by
  let x := ((n:ℝ)+1/2)*(s*centerAngle K)
  have hx : 0<x := by dsimp [x];positivity
  have habs : 0 < |t| := abs_pos.mpr ht.ne
  have hmw : 0<m*(s*centerAngle K) := by positivity
  have hprod : m*(s*centerAngle K)<4*|t| *x := by
    have hh := mul_lt_mul_of_pos_right hlarge (mul_pos hs hω)
    dsimp [x]
    nlinarith [mul_pos habs (mul_pos hs hω)]
  have hsq := (sq_le_sq₀ hmw.le (by positivity : 0≤4*|t| *x)).mpr hprod.le
  have hratio : D.Ck/x^2≤16*D.Ck*|t|^2/(m*(s*centerAngle K))^2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hx) (sq_pos_of_pos hmw)).mpr
    have hh := mul_le_mul_of_nonneg_left hsq D.Ck_pos.le
    nlinarith
  calc
    _≤D.hat x := by
      have hh := mul_le_mul_of_nonneg_right (Real.cos_le_one (((n:ℝ)+1/2)*centerAngle K))
        (D.hat_mem x).1
      simpa only [one_mul] using hh
    _≤D.Ck/x^2 := (le_abs_self _).trans (D.decay hx.ne')
    _≤16*D.Ck*|t|^2/(m*(s*centerAngle K))^2 := hratio
    _=D.longConstant*(|t|/(m*(s*centerAngle K)))^2 := by
      unfold KernelData.longConstant
      rw [div_pow]
      ring

theorem all_phase_lags {K : ℕ} (hK : 3≤K) {s t η d : ℝ}
    (hs : 0<s) (hs1 : s≤canonicalKernel.s1) (ht : t<0) (hη : 0<η) (hη1 : η<1)
    (hd : 0≤d) (hdm : d≤bandMargin canonicalKernel K s/2)
    (hsmall : canonicalKernel.longConstant*(|t|/(bandMargin canonicalKernel K s*(s*centerAngle K)))^2+d<
      Real.sqrt η/8)
    (Θ : C(Frequency,ℝ))
    (hdef : ∀ᵐ (c : Frequency) ∂(bandSpectrum (centerAngle K) (s*centerAngle K):Measure Frequency),
      |Real.arccos (c:ℝ)-2*Θ c|≤d) :
    0<phaseMean (bandSpectrum (centerAngle K) (s*centerAngle K)) Θ ∧
    (∀ n : ℕ,1≤n → phaseUpper (bandSpectrum (centerAngle K) (s*centerAngle K)) Θ n<
      eMinus η (n*|t|)*phaseMean (bandSpectrum (centerAngle K) (s*centerAngle K)) Θ) ∧
    (∀ n : ℕ,2≤n → phaseLower (bandSpectrum (centerAngle K) (s*centerAngle K)) Θ n<
      ePlus η (n*|t|)*phaseMean (bandSpectrum (centerAngle K) (s*centerAngle K)) Θ) := by
  let ω := centerAngle K
  let w := s*ω
  let ν := bandSpectrum ω w
  let G₀ := Real.cos (ω/2)*canonicalKernel.hat (w/2)
  let m := bandMargin canonicalKernel K s
  have hω : 0<ω := centerAngle_pos hK
  have hw : 0<w := mul_pos hs hω
  obtain ⟨hlo,hhi⟩ := band_endpoints hK hs hs1
  have hcos (ζ : ℝ) : cosAverage ν ζ=Real.cos (ζ*ω)*canonicalKernel.hat (ζ*w) :=
    bandSpectrum_cos_average ω hw hlo hhi ζ
  have hm : 0<m := bandMargin_pos canonicalKernel hK hs
  have hm4 : m≤1/4 := bandMargin_le_quarter _ _ _
  have hhalf : 1/2≤canonicalKernel.hat (w/2) := by
    have hp : 0<w/2 := by positivity
    have hu : w/2≤canonicalKernel.a0 := by
      have hh := mul_le_mul hs1 (centerAngle_le hK) hω.le canonicalKernel.s1_pos.le
      have ht := canonicalKernel.s1_scale_le_a0
      dsimp [w,ω] at *
      nlinarith
    exact canonicalKernel.hat_half hp hu
  have hcc := half_center_cos_ge hK
  change (1/2:ℝ)≤Real.cos (ω/2) at hcc
  have hG₀ : 1/4≤G₀ := by
    have hh := mul_le_mul hcc hhalf (by norm_num : (0:ℝ)≤1/2) (by linarith : 0≤Real.cos (ω/2))
    dsimp [G₀]
    nlinarith
  have hG₀1 : G₀≤1 := by
    have hh := mul_le_mul_of_nonneg_left (canonicalKernel.hat_mem (w/2)).2
      (by linarith : 0≤Real.cos (ω/2))
    dsimp [G₀]
    nlinarith [Real.cos_le_one (ω/2)]
  have hbase : G₀-d/2≤phaseMean ν Θ := by
    have hh := (abs_le.mp (phaseMean_error ν Θ hdef)).1
    rw [hcos] at hh
    dsimp [G₀]
    have heω : (1/2:ℝ)*ω=ω/2 := by ring
    have hew : (1/2:ℝ)*w=w/2 := by ring
    rw [heω,hew] at hh
    linarith
  have hGpos : 0<phaseMean ν Θ := by linarith
  refine ⟨hGpos,?_,?_⟩
  · intro n hn
    apply upper_lag_bound hm hm4 hd hdm (by positivity) hG₀ hG₀1 hbase hη hη1 hsmall
    · intro _
      have he := (abs_le.mp (phaseUpper_error ν Θ hdef n)).2
      rw [hcos] at he
      have hh := fourier_margin canonicalKernel hK hn hs hs1
      change m≤G₀-Real.cos (((n:ℝ)+1/2)*ω)*canonicalKernel.hat (((n:ℝ)+1/2)*w) at hh
      linarith
    · intro hlarge
      have he := (abs_le.mp (phaseUpper_error ν Θ hdef n)).2
      rw [hcos] at he
      have hh := ideal_upper_decay canonicalKernel hω hs ht hm hlarge
      linarith
  · intro n hn
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n≠0 by omega)
    have hk : 1≤k := by omega
    apply lower_lag_bound hm hm4 hd hdm (by positivity) hG₀ hbase hη1
    have he := (abs_le.mp (phaseLower_error ν Θ hdef k)).2
    rw [hcos] at he
    have hh := fourier_margin canonicalKernel hK hk hs hs1
    change m≤G₀-Real.cos (((k:ℝ)+1/2)*ω)*canonicalKernel.hat (((k:ℝ)+1/2)*w) at hh
    linarith

end
end nesterov.Spread
