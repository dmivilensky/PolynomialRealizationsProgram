import chebyshev1.Nonlinear.SecondOrder

/-! The leading radius is the attained maximum of the actual prefix residual. -/
namespace chebyshev1.Nonlinear
noncomputable section
open Polynomial

theorem leadingRadius_isGreatest (J : JacobiData) (I : SpectralInterval) {N s : ℕ}
    (ha : J.Admissible I N) (hm : J.EndpointMax N) (hs : s≤N) :
    IsGreatest {r : ℝ | ∃ lam ∈ Set.Icc I.mu I.L, r=|(J.residual I s).eval lam|}
      (leadingRadius J I s) := by
  have hp : 0≤(J.leading s).eval 1 :=
    (abs_nonneg _).trans (hm 0 s (by omega) 1 (by norm_num))
  constructor
  · refine ⟨I.mu,⟨le_rfl,I.mu_lt_L.le⟩,?_⟩
    rw [J.residual_eval,I.z_mu,abs_div,abs_of_nonneg hp,abs_of_pos (ha s hs)]
    rfl
  · rintro r ⟨lam,hlam,rfl⟩
    rw [J.residual_eval,abs_div,abs_of_pos (ha s hs)]
    exact div_le_div_of_nonneg_right (hm 0 s (by omega) _ (I.z_mem hlam)) (ha s hs).le

end
end chebyshev1.Nonlinear
