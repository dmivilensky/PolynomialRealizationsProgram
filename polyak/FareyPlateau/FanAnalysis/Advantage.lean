import polyak.FareyPlateau.FanAnalysis.Orders
import polyak.Global.Threshold.GlobalStructure

/-! Negative edge curvature gives a strictly better actual full-program
shift through an arbitrarily fine feasible Farey pair. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis
open General Levels ModeLocking Set

theorem delta_ne_zero (P : Fan.Data) : P.delta≠0 := by
  unfold Fan.Data.delta
  have hs : (P.sign:ℝ)≠0 := by rcases P.sign_unit with h|h <;> simp [h]
  have hk : (P.k:ℝ)≠0 := by exact_mod_cast (show P.k≠0 by have := P.period_ge; omega)
  have hL : (P.L:ℝ)≠0 := by exact_mod_cast (show P.L≠0 by have := P.period_ge; have := P.order_gt; omega)
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hs) (mul_ne_zero hk hL)

namespace Actual
variable {q : Tuning} {j k : ℕ} (A : Edge.AdjacentData q j k)

theorem critical_pos (hF : deriv^[2] A.function A.frequency<0) : 0<critical A := by
  have hkR : (3:ℝ)≤k := by exact_mod_cast A.period_ge
  have hs : 0<Real.sin (Real.pi/k) := Real.sin_pos_of_pos_of_lt_pi
    (by positivity) ((div_lt_iff₀ (by positivity : (0:ℝ)<k)).mpr (by nlinarith [Real.pi_pos]))
  unfold critical
  exact div_pos (mul_pos_of_neg_of_neg (by linarith) hF) (by positivity)

theorem negative_curvature_advantage (hF : deriv^[2] A.function A.frequency<0) :
    Threshold.sigma q<A.edgeShift := by
  have he : 0<critical A/2 := div_pos (critical_pos A hF) (by norm_num)
  obtain ⟨P,hj,hk,_,hfeasible⟩ := exists_fan_delta A.period_ge A.inverse 1 A.inverse_mod
    (Or.inl rfl) (fan_feasible_small A (show critical A/2<critical A by linarith))
  obtain ⟨a,c,_,_,hsol⟩ := hfeasible P hj hk rfl
  have hs : Threshold.sigma q≤A.edgeShift-critical A/2*P.delta^2 :=
    (Threshold.shifted_fp_iff q _).mp ⟨_,hsol⟩
  exact hs.trans_lt (sub_lt_self _ (mul_pos he (sq_pos_of_ne_zero (delta_ne_zero P))))

theorem negative_curvature_edge_interior (hF : deriv^[2] A.function A.frequency<0)
    (hs : A.edgeShift=0) : q∈interior {p : Tuning | Threshold.sigma p≤0} := by
  have hneg : Threshold.sigma q<0 := by simpa only [hs] using negative_curvature_advantage A hF
  have ho : IsOpen {p : Tuning | Threshold.sigma p<0} :=
    isOpen_lt Global.Threshold.continuous_sigma continuous_const
  exact (ho.subset_interior_iff.mpr (fun p (hp : Threshold.sigma p<0)=>hp.le)) hneg

end Actual
end polyak.FareyPlateau.FanAnalysis
