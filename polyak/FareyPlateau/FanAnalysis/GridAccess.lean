import polyak.FareyPlateau.FanAnalysis.Periodicity

/-! Every integer grid site is represented by an actual signed lag. -/
noncomputable section
namespace polyak.FareyPlateau.Fan.Data

theorem access_origin (P : Fan.Data) (r : ℤ) :
    ∃ n l : ℤ, (n : ℝ)*P.near = (r : ℝ)*P.k*P.delta + (l : ℝ)*(2*Real.pi) := by
  obtain ⟨a, b, hab⟩ := P.near_reduced
  refine ⟨-P.sign*r*a, P.sign*r*b, ?_⟩
  have hk : (P.k : ℝ) ≠ 0 := by exact_mod_cast (show P.k ≠ 0 by have := P.period_ge; omega)
  have hL : (P.L : ℝ) ≠ 0 := by exact_mod_cast (show P.L ≠ 0 by have := P.period_ge; have := P.order_gt; omega)
  have habR : (a : ℝ)*P.J+(b : ℝ)*P.L=1 := by exact_mod_cast hab
  unfold near delta
  push_cast
  field_simp
  linear_combination -(P.sign : ℝ)*(r : ℝ)*habR

end polyak.FareyPlateau.Fan.Data
