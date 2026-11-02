import jacobi.Variational.MultiplierRule
import jacobi.Variational.SecondActivity
import jacobi.Young.PotentialRegularity

/-!
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Every actual nonzero radial minimizer has the printed positive normal
multipliers, active second-moment threshold, mass complementarity and
positive-part Euler equation with the actual exponential potential.
All expansion, dilation, qualification and pointwise-test obligations are
discharged by the proved common variational theory.
Source: the normal multiplier rule and the exact actual G_2 variation.
Use: the second-moment gradient satisfies the boundedness premise of the common multiplier rule.
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real Filter Set jacobi.Young
set_option backward.isDefEq.respectTransparency false

/-- The actual exponent-two Green potential is bounded pointwise by the total mass.
Use: the second-moment gradient satisfies the boundedness premise of the common multiplier rule.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: the actual exponential kernel is at most one; integrate against the nonnegative density. -/
theorem potential_le_mass (m : Density) (x : ℝ) : potential m x≤m.mass := by
  rw [potential_kernel]
  apply integral_mono (second_inner_integrable m.integrable x) m.integrable
  intro y
  exact mul_le_of_le_one_right (m.nonneg y)
    (exp_le_one_iff.mpr (by linarith [abs_nonneg (x-y)]))

/-- The actual exponential Green potential of a nonzero density is strictly positive everywhere.
Use: semilinear classification excludes the zero solution for the actual optimizing potential.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: a zero value of the nonnegative convolution would make its integrand
vanish a.e. Its exponential factor is everywhere positive, forcing the actual mass to be zero. -/
theorem potential_pos (m : Density) (hm : 0<m.mass) (x : ℝ) : 0<potential m x := by
  -- The argument uses only integrability and positive actual mass.
  apply lt_of_le_of_ne (potential_nonneg m x)
  intro hz
  rw [potential_kernel] at hz
  have he := (integral_eq_zero_iff_of_nonneg (fun y => mul_nonneg (m.nonneg y) (exp_pos _).le)
    (second_inner_integrable m.integrable x)).mp hz.symm
  have hmzero : m.value=ᵐ[volume] 0 := he.mono fun _ h => (mul_eq_zero.mp h).resolve_right (exp_ne_zero _)
  have hmass : m.mass=0 := by simpa only [Density.mass,Pi.zero_apply,integral_zero] using integral_congr_ae hmzero
  exact hm.ne' hmass

/-- The actual signed second-moment linear term is the integral of its literal Green gradient.
Use: the common multiplier theorem sees the same gradient as the article's expansion.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: symmetry moves the signed perturbation to the outside integral,
then the absolutely convergent Fubini formula identifies the inner potential. -/
theorem second_gradient_pairing (m q : Density) :
    2*secondPairing m.value (q.value-m.value)=
      ∫ x,(2*potential m x)*(q.value x-m.value x) := by
  -- Signed perturbations remain integrable before changing integration order.
  rw [secondPairing_symm m.integrable (q.integrable.sub m.integrable) m.measurable
    (q.measurable.sub m.measurable),secondPairing_iterated (q.integrable.sub m.integrable)
      m.integrable (q.measurable.sub m.measurable) m.measurable,← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only [Pi.sub_apply]
    rw [← potential_kernel]
    ring

/-- Every actual radial second-moment minimizer has the complete normal pointwise KKT equation.
Use: starts the elliptic ODE and exact mass/second-moment normalization from an attained actual minimizer.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: the actual second expansion has remainder norm(delta)_1² and its
gradient is continuous bounded 2W_2. Strict dilation is already proved.
The normal cone theorem constructs positive multipliers, while amplitude
descent proves the second-moment threshold active. -/
theorem second_minimizer_kkt {M T : ℝ} (hT : 0<T) (m : Density) (hm : 0<m.mass)
    (hrad : SymmetricDecreasing m.value) (hmM : m.mass≤M) (hmT : T≤observe m .second)
    (hmin : m.cost=relaxedInfimum {Observation.second} M (fun _ => T)) :
    observe m .second=T ∧ ∃ μ l : ℝ,0<μ ∧ 0≤l ∧ l*(M-m.mass)=0 ∧
      (fun x => sqrt (m.value x))=ᵐ[volume] fun x => (2/3:ℝ)*max (2*μ*potential m x-l) 0 := by
  -- All multiplier premises are established for the original density and actual spectral constraint.
  have hminE (q : Density) (hqM : q.mass≤M) (hqT : T≤observe q .second) : m.energy≤q.energy := by
    have hcost : m.cost≤q.cost := by
      rw [hmin]
      apply sInf_le
      refine ⟨q,⟨hqM,?_⟩,rfl⟩
      intro i hi
      have hh : i=Observation.second := mem_singleton_iff.mp hi
      subst i
      exact hqT
    exact (ENNReal.ofReal_le_ofReal_iff q.energy_nonneg).mp hcost
  obtain ⟨k,hk,hgain⟩ := second_strict_dilation m hm
  have hγB (x : ℝ) : |2*potential m x|≤2*m.mass := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) (potential_nonneg m x))]
    linarith [potential_le_mass m x]
  have hvar (q : Density) (_hsmall : (∫ x,|q.value x-m.value x|)≤1) :
      |observe q .second-observe m .second-(∫ x,(2*potential m x)*(q.value x-m.value x))|≤
        (1:ℝ)*(∫ x,|q.value x-m.value x|)^2 := by
    rw [← second_gradient_pairing,one_mul]
    exact second_expansion_remainder m q
  obtain ⟨μ,l,hμ,hl,hcomp,heq⟩ := normal_multiplier_rule m hm hrad
    (fun q => observe q .second) (fun x => 2*potential m x)
    (measurable_const.mul (potential_continuous m).1.measurable) hγB
    zero_lt_one zero_lt_one hk hmM hmT hminE hvar hgain
  refine ⟨second_constraint_active hT m hmM hmT hmin,μ,l,hμ,hl,hcomp,?_⟩
  convert heq using 1
  funext x
  congr 2
  ring

/-- The actual subcritical second-moment infimum has a radial attainer satisfying its proved Euler equation.
Use: the elliptic calibration begins with an actual attained solution, without an assumed KKT certificate.
Article: jacobi, Appendix D.1 (moment multipliers and clipped profiles).
Proof: construct the actual direct-method minimizer with active constraint,
then apply the fully discharged KKT theorem to that same density. -/
theorem second_minimizer_kkt_exists {M T : ℝ} (hM : 0<M) (hT : 0<T) (hsub : T<M^2) :
    ∃ m : Density,SymmetricDecreasing m.value ∧ 0<m.mass ∧ m.mass≤M ∧
      observe m .second=T ∧ m.cost=relaxedInfimum {Observation.second} M (fun _ => T) ∧
      ∃ μ l : ℝ,0<μ ∧ 0≤l ∧ l*(M-m.mass)=0 ∧
        (fun x => sqrt (m.value x))=ᵐ[volume] fun x => (2/3:ℝ)*max (2*μ*potential m x-l) 0 := by
  -- Existence, activity and multipliers all concern one common actual minimizer.
  obtain ⟨m,hs,hm,hmM,hmT,hmin⟩ := second_minimizer_exists hM hT hsub
  exact ⟨m,hs,hm,hmM,hmT,hmin,(second_minimizer_kkt hT m hm hs hmM hmT.ge hmin).2⟩

end
end jacobi.Variational
