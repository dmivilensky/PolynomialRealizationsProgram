import polyak.FareyPlateau.LargeCurvature.ZoneA
import polyak.FareyPlateau.Ray.SecondMoment

noncomputable section
namespace polyak.FareyPlateau.LargeCurvature
open General Levels Set
open scoped BigOperators
namespace SourceData
variable {q : Tuning} {j k : ℕ} (B : SourceData q j k)

def sourceCertificate : Ray.SourceCertificate j k B.inverse B.D where
  card := 3
  lag := B.n
  weight := B.w
  admissible := B.admissible

theorem inverse_product : (B.inverse*(j:ℤ))%(k:ℤ)=1 := by
  simpa only [Int.ModEq,Int.emod_eq_of_lt (by norm_num : (0:ℤ)≤1)
    (by have := B.period_ge; omega : (1:ℤ)<k)] using B.inverse_mod

theorem oneMass : Ray.oneMass k B.inverse B.n B.w=1 := by
  have hbmod : B.inverse%(k:ℤ)=B.inverse := Int.emod_eq_of_lt B.inverse_pos.le B.inverse_lt
  have he : Ray.oneClass k B.inverse B.n=Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i _
    rw [B.classes,hbmod]
  rw [Ray.oneMass,he,B.normalization]

theorem curvatureMoment : Ray.curvatureMoment B.n B.w B.bar=
    4*(∑ i,B.w i*deviation B.n₀ k B.bar i^2) := by
  have hm := second_moment (n := (B.n₀:ℝ)) B.kp.ne' (s := B.bar)
  have he : Ray.curvatureMoment B.n B.w B.bar=(∑ i,B.w i*(B.n i:ℝ)^2)-B.bar^2 := by
    rw [Ray.curvatureMoment,←B.mean]
    simp only [Fin.sum_univ_succ]
    ring
  rw [he]
  simp only [n,integerLag_cast,Int.cast_natCast]
  change (∑ i,B.w i*lag B.n₀ k i^2)=B.bar^2+4*(∑ i,B.w i*deviation B.n₀ k B.bar i^2) at hm
  linarith only [hm]

theorem variance_strict : 4*(∑ i,B.w i*deviation B.n₀ k B.bar i^2) <
    2*sineMargin k*B.mA := by
  let V := ∑ i,B.w i*deviation B.n₀ k B.bar i^2
  let U := (4/3)*(∑ i,B.w i*|deviation B.n₀ k B.bar i|^3)*zoneRadius k B.N
  have hV : 0 ≤ V := Finset.sum_nonneg (fun i _=>by positivity [B.positive i])
  have hU : 0 ≤ U := by
    dsimp [U]
    apply mul_nonneg _ (by unfold zoneRadius; positivity [B.kp,B.N_pos])
    have hsum : 0 ≤ ∑ i,B.w i*|deviation B.n₀ k B.bar i|^3 :=
      Finset.sum_nonneg (fun i _=>mul_nonneg (B.positive i).le (pow_nonneg (abs_nonneg _) _))
    exact mul_nonneg (by norm_num) hsum
  have hC := B.centralCoefficient_neg
  change -2*sineMargin k*B.mA/Real.pi+2*V+U<0 at hC
  have hp := mul_neg_of_neg_of_pos hC Real.pi_pos
  have he : (-2*sineMargin k*B.mA/Real.pi+2*V+U)*Real.pi=
      -2*sineMargin k*B.mA+2*V*Real.pi+U*Real.pi := by field_simp
  rw [he] at hp
  have hπ : (2:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hh := mul_le_mul_of_nonneg_left hπ (show 0 ≤ 2*V by positivity)
  have hu := mul_nonneg hU Real.pi_pos.le
  change 4*V<2*sineMargin k*B.mA
  linarith

theorem curvature : deriv^[2] (indexedSymbol q 0 B.n B.w) B.ω < 0 := by
  have hjet := B.sourceCertificate.second_moment (by have := B.numerator_ge; omega)
    B.numerator_lt B.inverse_product q B.coefficients
  change deriv^[2] (indexedSymbol q 0 B.n B.w) B.ω =
    Real.cos B.c*Ray.curvatureMoment B.n B.w B.bar-
      2*Real.sin B.c*deriv^[2] (Geometry.shiftedAngle q 0) B.ω*
        Ray.oneMass k B.inverse B.n B.w at hjet
  rw [hjet,B.curvatureMoment,B.oneMass,mul_one]
  have hθ : B.mA ≤ deriv^[2] (Geometry.shiftedAngle q 0) B.ω := by
    have hh := B.second_lower B.center_below
    rw [←iteratedDeriv_eq_iterate,(B.phase_actual_eventually B.ω_mem).iteratedDeriv_eq 2,
      iteratedDeriv_eq_iterate] at hh
    exact hh
  have hs : sineMargin k ≤ Real.sin B.c := by
    have hh := B.tangent_sine (B.below_in_window B.center_below)
    simpa only [sub_self,mul_zero,zero_div,add_zero] using hh
  have hV : 0 ≤ 4*(∑ i,B.w i*deviation B.n₀ k B.bar i^2) :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _=>mul_nonneg (B.positive i).le (sq_nonneg _)))
  have hcos := mul_le_of_le_one_left hV (Real.cos_le_one B.c)
  have hsin := mul_le_mul hs hθ B.mA_pos.le ((sineMargin_pos B.kr).le.trans hs)
  linarith [B.variance_strict]

end SourceData
end polyak.FareyPlateau.LargeCurvature
