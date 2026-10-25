import chebyshev1.SineJacobi.ProfileODE
import chebyshev1.Analysis.SingularUniqueness

/-!
Article: chebyshev1, Theorem E.3.
The solution and boundary normalization stated in E.3 determine the profile uniquely.
Result: `chebyshev1.SineJacobi.sineProfile_unique` supplies the stated article conclusion.
-/
namespace chebyshev1.SineJacobi
noncomputable section
open Real Set Filter Topology

/--
The solution and boundary normalization stated in E.3 determine the profile uniquely.

Pointwise equality on the specified domain: `EqOn g sineProfile (Ioo 0 1)`.

Use: the ordered `Article` showcase checks this article-facing formulation directly.

Article: chebyshev1, Theorem E.3.

Proof: Use the identities/estimates `chebyshev1.Analysis.singular_sqrt_unique`,
`chebyshev1.SineJacobi.sineProfile_deriv`,
`chebyshev1.SineJacobi.sineProfile_explicit_ode` with the arguments shown in the proof.
-/
theorem sineProfile_unique {g : ℝ → ℝ}
    (hg : DifferentiableOn ℝ g (Ioo 0 1))
    (hg' : DifferentiableOn ℝ (deriv g) (Ioo 0 1))
    (hODE : ∀ t ∈ Ioo (0:ℝ) 1,
      deriv (deriv g) t+Real.pi^2/(4*sin (Real.pi*t)^2)*g t = 0)
    (hb : Tendsto (fun t => g t/sqrt t) (𝓝[>] 0) (𝓝 1)) :
    EqOn g sineProfile (Ioo 0 1) := by
  -- Use the identities/estimates `chebyshev1.Analysis.singular_sqrt_unique`,
  -- `chebyshev1.SineJacobi.sineProfile_deriv`,
  -- `chebyshev1.SineJacobi.sineProfile_explicit_ode` with the arguments shown in the
  -- proof.
  apply chebyshev1.Analysis.singular_sqrt_unique (f' := sineProfile₁) (g' := deriv g)
    (q := fun t => Real.pi^2/(4*sin (Real.pi*t)^2))
  · exact fun t ht => sineProfile_deriv ht
  · intro t ht
    have he := sineProfile_explicit_ode ht
    convert sineProfile₁_deriv ht using 1
    linarith
  · intro t ht
    exact ((hg t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt
  · intro t ht
    have hd := ((hg' t ht).differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt
    convert hd using 1
    linarith [hODE t ht]
  · exact fun t ht => sineProfile_pos ht
  · exact sineProfile_boundary
  · exact hb

end
end chebyshev1.SineJacobi
