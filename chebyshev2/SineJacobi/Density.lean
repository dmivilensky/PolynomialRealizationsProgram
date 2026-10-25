import chebyshev1.SineJacobi.ProfileNormalization

/-!
Article: chebyshev2, Theorem 2.5 and Section 4.3, The sine energy.
Use: share the original sine density and energy between finite and continuum proofs.
The original sine density and its actual squared integral are shared
by the finite comparisons and the analytic sine--Legendre realization.
These definitions require the proved original integral normalization;
they do not require the separate decimal certification of that integral.
-/
namespace chebyshev2.SineJacobi
noncomputable section

/-- The original normalized sine--Jacobi density from the first article.
Use: SineJacobi.Profile gives its elliptic formula and SineContinuum.Profiles identifies twice the actual Green diagonal; jacobi.GelfandLevitan.SineCase identifies the alpha=-1/2 persymmetric profile with this same density.
Article: chebyshev2, Theorem 2.5; chebyshev1, Theorem 5.1; jacobi, §2, special case of Theorem P. -/
abbrev phi : ℝ → ℝ := chebyshev1.SineJacobi.sineDensity

/-- The actual squared-density integral defining the sine energy.
Use: SineJacobi.Profile gives its integral formula, SineJacobi.Finite adds the separate decimal bound and jacobi.GelfandLevitan.SineCase identifies c_star(-1/2) with this original integral.
Article: chebyshev2, Section 4.3, The sine energy; chebyshev1, Theorem 5.1; jacobi, §2, c_star(-1/2)=c_sin. -/
abbrev energy : ℝ := chebyshev1.SineJacobi.sineEnergy

end
end chebyshev2.SineJacobi
