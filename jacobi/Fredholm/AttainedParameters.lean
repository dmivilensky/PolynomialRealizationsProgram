import jacobi.Fredholm.DeterminantQuadrature
import jacobi.Fredholm.EdgeTarget
import jacobi.Fredholm.ExtendedEnergy

/-!
Article: jacobi, Theorem D.7.
Every stated edge spectrum has an actual optimizer and an actual printed
parameter pair. The original objective and both constraints are evaluated
without auxiliary existence, pole-margin or profile hypotheses. This is
the necessity and attainment direction; uniqueness and sufficiency of an
arbitrary normalized pair are separate parameter-calculus obligations.
Source: the actual direct method, normal multiplier rule and Green quadratures.
Use: records the exhaustive necessary alternatives supplied by a genuine optimizing profile.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Variational
set_option backward.isDefEq.respectTransparency false

/-- The actual interior-or-free parameter constraints appearing in the Fredholm minimum.
Use: records the exhaustive necessary alternatives supplied by a genuine optimizing profile.
Article: jacobi, Theorem D.7.
-/
def admissibleParameters (s M d t c : ℝ) : Prop :=
  t∈Ioc (0:ℝ) 1 ∧ c∈Ioo (0:ℝ) 1 ∧ determinant t c=d ∧ mass t c≤s*M ∧
    (t<1 → mass t c=s*M)

/-- The actual active extended determinant is its positive finite real threshold.
Use: the literal normalized determinant quadrature equals the original d, without an extra active-real premise.
Article: jacobi, Theorem D.7.
Proof: the actual pole margin identifies the determinant with ofReal of
its real spectral sum, whose summands are nonnegative; ofReal is injective
on these nonnegative values and the stated positive threshold. -/
theorem Optimizer.real_active {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) (hd : 0≤d) :
    P.density.fredholmReal s=d := by
  have hnon : 0≤P.density.fredholmReal s := tsum_nonneg fun j =>
    fredholmLog_nonneg (by
      have hh := P.density.spectral_margin hs.le
        (by linarith : s*observe P.density .top≤1-(1-s*observe P.density .top)) j
      linarith [P.pole])
  have h := P.active
  rw [P.density.fredholm_eq hs.le (sub_pos.mpr P.pole) (by linarith)] at h
  exact (ENNReal.ofReal_eq_ofReal_iff hnon hd).mp h

/-- The true optimizing parameters satisfy the exhaustive printed interior-or-free constraints.
Use: proves existence of at least one admissible printed alternative from actual variational data.
Article: jacobi, Theorem D.7.
Proof: the actual determinant quadrature and activity give its defining
equation. The mass quadrature gives the upper bound. Strict tau<1 excludes
the zero mass multiplier, so genuine complementarity saturates mass. -/
theorem Optimizer.admissible {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) (hd : 0≤d) :
    admissibleParameters s M d (P.tau hs) (P.chi hs) := by
  -- Both branch constraints are consequences of actual normal multipliers.
  have hp := P.parameters hs
  refine ⟨hp.1,hp.2,(P.determinant_quadrature hs).symm.trans (P.real_active hs hd),?_,?_⟩
  · rw [← P.mass_quadrature hs]
    exact mul_le_mul_of_nonneg_left P.mass_le hs.le
  · intro ht
    have hell : P.ell≠0 := by
      intro hz
      have hh := (P.free_iff hs).1.mpr ((P.free_iff hs).2.mpr hz)
      exact ht.ne hh
    have hm : P.density.mass=M := (sub_eq_zero.mp
      ((mul_eq_zero.mp P.complementary).resolve_left hell)).symm
    rw [← P.mass_quadrature hs,hm]

/-- The actual attained Fredholm infimum has exactly the normalized printed value at its genuine parameters.
Use: evaluates the true variational value before proving uniqueness or constructing arbitrary candidate pairs.
Article: jacobi, Theorem D.7.
Proof: the actual objective quadrature fixes the positive coupling scale;
divide by that nonzero scale and use the genuine attainment equality. -/
theorem Optimizer.value {s M d : ℝ} (P : Optimizer s M d) (hs : 0<s) :
    fredholmInfimum s M (ENNReal.ofReal d)=
      ENNReal.ofReal (energy (P.tau hs) (P.chi hs)/(2*s)^(3/2:ℝ)) := by
  rw [← P.optimal]
  apply congrArg ENNReal.ofReal
  exact (eq_div_iff (rpow_pos_of_pos (by positivity : 0<2*s) (3/2:ℝ)).ne').mpr
    (by simpa only [mul_comm] using P.energy_quadrature hs)

/-- Every actual admissible edge spectrum has a genuine optimizer with an attained printed parameter pair and exact normalized cost.
Use: discharges all variational, spectral-pole and quadrature premises in the necessity half of the Fredholm theorem.
Article: jacobi, Theorem D.7.
Proof: the original edge target is strictly positive, finite and strictly
below its scalar mass threshold by the complete Fredholm moment series.
The actual direct method therefore produces a canonical optimizer. Its
proved quadratures and complementarity give both asserted conclusions. -/
theorem edge_attained_parameters (Λ : EdgeSpectrum) {s : ℝ} (hs : 0<s) (hp : s*Λ.value 0<1) :
    ∃ P : Optimizer s Λ.mass (target Λ s),
      admissibleParameters s Λ.mass (target Λ s) (P.tau hs) (P.chi hs) ∧
      extendedInfimum s Λ.mass (Λ.fredholm s)=
        ENNReal.ofReal (energy (P.tau hs) (P.chi hs)/(2*s)^(3/2:ℝ)) := by
  -- Every assumption of actual optimizer existence comes from the stated edge data.
  obtain ⟨P⟩ := optimizer_exists hs Λ.mass_pos (edge_target_pos Λ hs hp) (edge_target_subcritical Λ hs hp)
  refine ⟨P,P.admissible hs (edge_target_pos Λ hs hp).le,?_⟩
  rw [extendedInfimum_eq,edge_target_eq Λ hs.le hp]
  exact P.value hs

end
end jacobi.Fredholm
