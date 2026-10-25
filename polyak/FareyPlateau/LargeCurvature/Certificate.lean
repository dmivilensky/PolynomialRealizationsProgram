import polyak.FareyPlateau.LargeCurvature.Curvature
import polyak.FareyPlateau.LargeCurvature.Endpoint

/-! The original explicit three-lag symbol satisfies all three strict
certificate conditions, including resonant slope indices. -/
noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open General Levels Set
open scoped BigOperators
namespace SourceData
variable {q : Tuning} {j k : ℕ} (B : SourceData q j k)

theorem middle_symbol {x : ℝ} (hx : x ∈ B.window)
    (hθ : Geometry.shiftedAngle q 0 x > Real.pi/2) : indexedSymbol q 0 B.n B.w x < 0 := by
  have htrim := B.window_trimmed hx
  have hp : 0 < Real.pi/(2*k) := div_pos Real.pi_pos (mul_pos (by norm_num) B.kp)
  have hxi : x ∈ Ioo (0:ℝ) Real.pi := ⟨by linarith [htrim.1],by linarith [htrim.2]⟩
  have hπ := (Geometry.shiftedAngle_mem q 0 hxi).2.le
  have hlag (i : Fin 3) : ModeLocking.lagExtension q 0 (B.n i) x < 0 := by
    have hh := lag_middle_zone (δ := x-B.ω) (θ := ModeLocking.TwoLag.phase q 0 x)
      (B.lag_phase i) (middle_zone_angles B.kr B.N_pos (B.lag_abs i) (B.window_delta hx))
      (by rwa [B.phase_eq ⟨hxi.1.le,hxi.2.le⟩])
      (by rwa [B.phase_eq ⟨hxi.1.le,hxi.2.le⟩])
    have he : Geometry.extendedLag (fun _=>ModeLocking.TwoLag.phase q 0 x) (B.n i) (B.ω+(x-B.ω))=
        ModeLocking.lagExtension q 0 (B.n i) x := by
      rw [show B.ω+(x-B.ω)=x by ring]
      simp only [ModeLocking.lagExtension,Geometry.extendedLag,ModeLocking.TwoLag.phase]
    rwa [he] at hh
  exact Finset.sum_neg (fun i _=>mul_neg_of_pos_of_neg (B.positive i) (hlag i)) Finset.univ_nonempty

theorem strict {x : ℝ} (hx : 0 < x ∧ x ≤ Real.pi) (hne : x ≠ B.ω) :
    indexedSymbol q 0 B.n B.w x < 0 := by
  by_cases hwin : x ∈ B.window
  · by_cases hbelow : x ∈ Geometry.phaseBelow q 0
    · exact (B.central_symbol_bound_actual hbelow).trans_lt
        (mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (sub_ne_zero.mpr hne)) B.centralCoefficient_neg)
    · have htrim := B.window_trimmed hwin
      have hp : 0 < Real.pi/(2*k) := div_pos Real.pi_pos (mul_pos (by norm_num) B.kp)
      have hxi : x ∈ Ioo (0:ℝ) Real.pi := ⟨hx.1,by linarith [htrim.2]⟩
      exact B.middle_symbol hwin (lt_of_not_ge (fun h=>hbelow ⟨hxi,h⟩))
  · exact B.far_symbol hx hwin

def certificate : Edge.Certificate q 0 j k :=
  indexedCertificate (by have := B.period_ge; omega) (by have := B.numerator_ge; omega)
    B.numerator_lt B.inverse B.inverse_pos B.inverse_lt B.inverse_mod B.n B.w B.injective B.nonzero
    B.positive B.normalization (fun i=>Or.inr (B.classes i))
    ⟨0,1,fun h=>(by norm_num : (0:Fin 3)≠1) (B.injective h),B.classes 0,B.classes 1⟩
    (by
      rw [Geometry.shiftedCurve_zero]
      exact source_edge_phase q (by have := B.numerator_ge; omega) B.numerator_lt B.coefficients)
    (fun x hx hp hne=>B.strict ⟨hx,hp⟩ hne) B.curvature B.endpoint

include B

theorem regular : ModeLocking.RegularPoint q 0 k := B.certificate.regular

theorem sigma_eq_zero : Threshold.sigma q=0 := B.certificate.sigma_eq

theorem sigmaPeriodic_eq_zero : Threshold.sigmaPeriodic q k=0 := B.certificate.sigmaPeriodic_eq

end SourceData
end polyak.FareyPlateau.LargeCurvature
