import jacobi.RootMass.ProfileSupport
import jacobi.RootMass.LocalGreen

/-!
Article: jacobi, Appendix D.5 (compact root-mass profile).
The full global minimum principle fixes an actual compact representative,
including its harmless endpoint values. The original integral potential is
preserved. Its classical Green equation is recovered locally on the positive
core, without imposing continuity across the genuine free-boundary jump.
Source: the proved scalar minimum principle and local Green calculus.
Use: the actual compact density is its square on its proved positive core.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational jacobi.Young
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The continuous larger scalar root evaluated at the original integral potential.
Use: the actual compact density is its square on its proved positive core.
Article: jacobi, Appendix D.5 (compact root-mass profile).
-/
def branch (m : RootDensity) (a b mu x : ℝ) : ℝ := upperRoot b (coefficient m a b mu x)

/-- The literal compact representative selected by the actual minimum principle.
Use: its original Green potential gives the local ODE and matching condition.
Article: jacobi, Appendix D.5 (compact root-mass profile).
-/
def compactValue (m : RootDensity) (a b mu A : ℝ) : ℝ → ℝ :=
  (Icc (-A) A).indicator (fun x => branch m a b mu x^2)

/-- The actual larger-root branch is continuous, including at both free boundaries.
Use: obtains local classical Green regularity of the compact optimizer.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: the original potential, square root and the polynomial operations are continuous. -/
theorem branch_continuous (m : RootDensity) (a b mu : ℝ) : Continuous (branch m a b mu) := by
  unfold branch upperRoot coefficient
  have hc : Continuous (fun x => -a*b/2+2*mu*potential m.toDensity x) :=
    continuous_const.add (continuous_const.mul (potential_continuous m.toDensity).1)
  exact (hc.add ((hc.pow 2).sub continuous_const).sqrt).div_const 3

/-- The actual larger root at the switching coefficient equals the boundary value b.
Use: fixes the compact profile's exact boundary normalization.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: the radicand at the switching level is b², whose nonnegative square root is b. -/
theorem upperRoot_switch {b : ℝ} (hb : 0≤b) : upperRoot b (2*b)=b := by
  unfold upperRoot
  rw [show (2*b)^2-3*b^2=b^2 by ring,sqrt_sq hb]
  ring

/-- The proved actual pointwise minimum principle identifies the original density with its compact formula almost everywhere.
Use: no guessed optimizer or stationarity certificate is assumed in the profile quadrature chain.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: remove the two null boundary points. In the core the unique global
minimizer is the larger root; outside it is zero. Squaring the actual
square root gives the original density in both regions. -/
theorem compactValue_ae {a b mu A : ℝ} (hb : 0<b) (m : RootDensity)
    (hcore : ∀ x : ℝ,2*b<coefficient m a b mu x ↔ |x|<A)
    (hout : ∀ x : ℝ,A< |x| → coefficient m a b mu x<2*b)
    (hP : ∀ᵐ x : ℝ,∀ n : ℝ,0≤n → h b (coefficient m a b mu x) (sqrt (m.value x))≤h b (coefficient m a b mu x) n) :
    m.value=ᵐ[volume] compactValue m a b mu A := by
  -- Endpoint values have no effect on any integral or spectral quantity.
  have hxA : ∀ᵐ x : ℝ,x≠A ∧ x≠-A :=
    (show ∀ᵐ x : ℝ,x≠A by simp [ae_iff]).and (show ∀ᵐ x : ℝ,x≠-A by simp [ae_iff])
  filter_upwards [hP,hxA] with x hx hne
  have hs := sq_sqrt (m.nonneg x)
  by_cases hi : x∈Icc (-A) A
  · have hlt : |x|<A := abs_lt.mpr ⟨lt_of_le_of_ne hi.1 (Ne.symm hne.2),lt_of_le_of_ne hi.2 hne.1⟩
    have he := minimizer_above hb ((hcore x).mpr hlt) (sqrt_nonneg _) hx
    rw [he] at hs
    simpa only [compactValue,indicator_of_mem hi,branch] using hs.symm
  · have habs : A< |x| := by
      have hn : ¬ |x|≤A := by simpa only [abs_le,mem_Icc] using hi
      exact lt_of_not_ge hn
    have he := minimizer_below (hout x habs) (sqrt_nonneg _) (hx 0 le_rfl)
    rw [he] at hs
    simpa only [compactValue,indicator_of_notMem hi,zero_pow (by decide : 2≠0)] using hs.symm

/-- The actual compact representative is a genuine nonnegative measurable finite-energy density.
Use: classical Green calculus applies to its literal core values while all original variational data are retained.
Article: jacobi, Appendix D.5 (compact root-mass profile).
-/
def compactDensity (m : RootDensity) (a b mu A : ℝ)
    (he : m.value=ᵐ[volume] compactValue m a b mu A) : Density :=
  m.toDensity.replace (compactValue m a b mu A)
    (((branch_continuous m a b mu).pow 2).measurable.indicator measurableSet_Icc)
    (fun x => by unfold compactValue; exact indicator_nonneg (fun _ _ => sq_nonneg _) x) he

/-- At every point strictly inside the proved core, the original potential satisfies its actual classical Green equation with the larger-root density.
Use: derives the first integral from the original minimizing problem.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: replace the source by its proved a.e. compact representative. Its
literal value is continuous near each interior point. Potential congruence
and uniqueness of the first derivative transfer the local Green equation. -/
theorem compactPotential_classical (m : RootDensity) (a b mu A : ℝ)
    (he : m.value=ᵐ[volume] compactValue m a b mu A) {x : ℝ} (hx : x∈Ioo (-A) A) :
    HasDerivAt (potentialSlope m.toDensity)
      (4*potential m.toDensity x-4*branch m a b mu x^2) x := by
  -- The density may jump at the boundary; only the actual interior neighborhood is used here.
  let q := compactDensity m a b mu A he
  have heq : q.value =ᶠ[𝓝 x] fun t => branch m a b mu t^2 := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
    change (Icc (-A) A).indicator (fun t => branch m a b mu t^2) t=_
    rw [indicator_of_mem (show t∈Icc (-A) A from ⟨ht.1.le,ht.2.le⟩)]
  have hc : ContinuousAt q.value x := ((branch_continuous m a b mu).pow 2).continuousAt.congr heq.symm
  have hp : potential m.toDensity=potential q := potential_congr he
  have hs : potentialSlope m.toDensity=potentialSlope q := by
    funext t
    have h := potential_hasDerivAt m.toDensity t
    rw [hp] at h
    exact h.unique (potential_hasDerivAt q t)
  rw [hs,hp]
  convert potential_second_derivative_at q hc using 1
  exact congrArg (fun r : ℝ => 4*potential q x-4*r) (heq.eq_of_nhds.symm)

end
end jacobi.RootMass
