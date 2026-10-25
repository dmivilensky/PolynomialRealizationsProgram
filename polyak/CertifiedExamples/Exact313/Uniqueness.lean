import polyak.CertifiedExamples.Exact313.Contacts

/-! Local uniqueness of the actual tuning on the certified ratio branch.
All four Hermite equations are primary fixed-frequency equations. -/
noncomputable section
namespace polyak.CertifiedExamples.Exact313
open General Levels ModeLocking.TwoLag

theorem unique_tuning_of_Hermite {q : Tuning} (hβ : 0<q.beta) {r : ℝ}
    (hr : r∈rootBox) (hr0 : 0≤r)
    (hv₁ : q.Xi c₁=Psi 4 r c₁) (hv₂ : q.Xi c₂=Psi 4 r c₂)
    (hd₁ : deriv q.Xi c₁=deriv (Psi 4 r) c₁)
    (hd₂ : deriv q.Xi c₂=deriv (Psi 4 r) c₂) : q=qStar := by
  have hG := G_eq_zero q 4 r c₁_lt_c₂.ne hv₁ hv₂ hd₁ hd₂
  have he : r=scalarRoot.value := scalarRoot.unique r hr ((compatibility_eq_zero_iff hr0).mpr hG)
  subst r
  have hc := Hermite_quadratic_unique q 4 c₁_lt_c₂.ne hv₁ hv₂ hd₁
    (A:=(coefficients scalarRoot.value).c2) (B:=(coefficients scalarRoot.value).c1)
    (D:=(coefficients scalarRoot.value).c0)
    (by convert (hermiteQuadratic_first 4 scalarRoot.value c₁ c₂).1 using 1
        dsimp [Chart.Coefficients.eval]
        ring)
    (by convert hermiteQuadratic_second_value 4 scalarRoot.value c₁_lt_c₂.ne using 1
        dsimp [Chart.Coefficients.eval]
        ring)
    (by convert contact_slopes_first using 1
        rw [(coefficients_hasDerivAt _ _).deriv]
        ring)
  apply Chart.coefficients_injective hβ qStar_positive_beta
  rw [qStar_coefficients]
  apply Chart.Coefficients.ext
  · exact hc.2.2.symm
  · exact hc.2.1.symm
  · exact hc.1.symm

end polyak.CertifiedExamples.Exact313
