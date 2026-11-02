import jacobi.GelfandLevitan.FullWaveRegularity
import jacobi.GelfandLevitan.TargetSpectralOperator

/-!
Article: jacobi, Theorem 2.1.
The genuine full self-adjoint target operator acts as the original
Schrodinger expression on arbitrary finite linear combinations of its
actual eigenfunctions. The ordinary derivatives and the physical L2
representatives are proved independently before they are identified.
Use: targetOperator_differential evaluates its true first and second derivatives and connects it to the actual original spectral operator.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- An arbitrary finite combination of the actual original target waves in real physical coordinates.
Use: targetOperator_differential evaluates its true first and second derivatives and connects it to the actual original spectral operator.
Article: jacobi, Theorem 2.1.
-/
def finiteTargetWave (a : ℝ) (ha : -1<a) (S : Finset ℕ) (c : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ n∈S,c n*fullWavePhysical a ha n t

/-- The same arbitrary finite target combination as a continuous original closed-interval function.
Use: finiteTargetState_toLp gives its actual L2 representative, without evaluating quotient vectors pointwise.
Article: jacobi, Theorem 2.1.
-/
def finiteTargetMap (a : ℝ) (ha : -1<a) (S : Finset ℕ) (c : ℕ → ℝ) : C(Interval,ℝ) :=
  ∑ n∈S,c n • fullWaveMap a ha n

/-- The arbitrary finite original target combination in the genuine full graph domain of H_alpha.
Use: targetOperator_differential proves the original classical differential action for every such state.
Article: jacobi, Theorem 2.1.
-/
def finiteTargetState (a : ℝ) (ha : -1<a) (S : Finset ℕ) (c : ℕ → ℝ) :
    (targetOperator a ha).domain :=
  ∑ n∈S,c n • (⟨fullTargetBasis a ha n,targetOperator_basis_mem a ha n⟩ : (targetOperator a ha).domain)

/-- The actual domain state has precisely its original finite spectral combination as its underlying L2 vector.
Use: finiteTargetState_toLp and finiteTargetState_action keep the same actual full-domain vector throughout the differential identification.
Article: jacobi, Theorem 2.1.
Proof: the genuine graph domain is a submodule, so its inclusion preserves the unchanged finite sums and real scalar factors. -/
theorem finiteTargetState_coe (a : ℝ) (ha : -1<a) (S : Finset ℕ) (c : ℕ → ℝ) :
    (finiteTargetState a ha S c:Space)=∑ n∈S,c n • fullTargetBasis a ha n := by
  simp only [finiteTargetState,Submodule.coe_sum,Submodule.coe_smul_of_tower]

/-- The genuine full target operator acts on every actual finite state by its original sigma-weighted spectral combination.
Use: targetOperator_differential compares this independently proved actual operator action with the original ordinary second derivatives.
Article: jacobi, Theorem 2.1.
Proof: apply the linear map on the genuine graph domain to the finite sum, then use the actual original eigenvector theorem. -/
theorem finiteTargetState_action (a : ℝ) (ha : -1<a) (S : Finset ℕ) (c : ℕ → ℝ) :
    targetOperator a ha (finiteTargetState a ha S c)=
      (finiteTargetState a ha S (fun n => c n* jacobi.Bessel.sigma a ha n):Space) := by
  rw [finiteTargetState_coe]
  change (targetOperator a ha).toFun (∑ n∈S,c n •
    (⟨fullTargetBasis a ha n,targetOperator_basis_mem a ha n⟩:(targetOperator a ha).domain))=_
  simp only [map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro n _
  change c n • targetOperator a ha ⟨fullTargetBasis a ha n,targetOperator_basis_mem a ha n⟩=_
  rw [targetOperator_basis,smul_smul]

/-- The actual continuous closed-interval target wave embeds as the genuine full target basis vector.
Use: finiteTargetState_toLp identifies all finite spectral combinations with their original continuous representatives.
Article: jacobi, Theorem 2.1.
Proof: both genuine quotient vectors have the independently proved actual continuous wave as their almost-everywhere representative. -/
theorem fullWaveMap_toLp (a : ℝ) (ha : -1<a) (n : ℕ) :
    ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume (fullWaveMap a ha n)=fullTargetBasis a ha n := by
  apply Lp.ext
  exact (ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) volume _).trans
    (fullTargetBasis_wave_ae a ha n).symm

/-- The genuine finite graph-domain target state is the actual L2 inclusion of its original continuous finite wave combination.
Use: targetOperator_differential transports the proved finite spectral action to actual physical representatives.
Article: jacobi, Theorem 2.1.
Proof: the continuous-function L2 inclusion is linear and every actual continuous basis wave has the independently proved original basis quotient vector. -/
theorem finiteTargetState_toLp (a : ℝ) (ha : -1<a) (S : Finset ℕ) (c : ℕ → ℝ) :
    (finiteTargetState a ha S c:Space)=ContinuousMap.toLp (𝕜 := ℝ) (p := 2) volume
      (finiteTargetMap a ha S c) := by
  simp only [finiteTargetState_coe,finiteTargetMap,map_sum,map_smul,fullWaveMap_toLp]

/-- The continuous and real-coordinate finite target combinations are exactly the same original physical function.
Use: targetOperator_differential transfers the actual L2 representatives to the original ordinary differential expression.
Article: jacobi, Theorem 2.1.
Proof: evaluate the continuous sum and use the proved original full-wave coordinate identity in each summand. -/
theorem finiteTargetMap_apply (a : ℝ) (ha : -1<a) (S : Finset ℕ) (c : ℕ → ℝ) (t : Interval) :
    finiteTargetMap a ha S c t=finiteTargetWave a ha S c t := by
  simp only [finiteTargetMap,finiteTargetWave,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    smul_eq_mul,fullWavePhysical_eq_map]

/-- Every actual finite combination of original full target waves is genuinely C2 on the original physical interior.
Use: finiteTargetWave_second_derivative and targetOperator_differential concern actual classical derivatives of every element of the original eigenfunction span.
Article: jacobi, Theorem 2.1.
Proof: sum the independently proved true C2 original waves multiplied by their unchanged real coefficients. -/
theorem finiteTargetWave_contDiffOn_two (a : ℝ) (ha : -1<a) (S : Finset ℕ) (c : ℕ → ℝ) :
    ContDiffOn ℝ 2 (finiteTargetWave a ha S c) (Ioo (0:ℝ) 1) :=
  ContDiffOn.sum (fun n _ => contDiffOn_const.mul (fullWavePhysical_contDiffOn_two a ha n))

/-- The true first derivative of an arbitrary finite target combination is the unchanged finite combination of actual original wave derivatives.
Use: finiteTargetWave_second_derivative differentiates this genuine identity locally on the physical interior.
Article: jacobi, Theorem 2.1.
Source: the derivative of a finite sum.
Proof: the genuine original C2 wave regularity supplies every derivative; apply the actual constant-multiple rule and finite-sum rule. -/
theorem finiteTargetWave_first_derivative (a : ℝ) (ha : -1<a) (S : Finset ℕ) (c : ℕ → ℝ)
    {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (finiteTargetWave a ha S c) (∑ n∈S,c n*deriv (fullWavePhysical a ha n) t) t :=
  HasDerivAt.fun_sum (fun n _ =>
    ((((fullWavePhysical_contDiffOn_two a ha n) t ht).contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt
      (by norm_num : (2:WithTop ℕ∞)≠0)).hasDerivAt.const_mul (c n))

/-- The genuine second derivative of each arbitrary finite original target combination is its actual original ODE acceleration sum.
Use: finiteTargetWave_equation and targetOperator_differential identify the true operator differential action throughout the original finite span.
Article: jacobi, Theorem 2.1.
Proof: the genuine first-derivative identity holds on a physical neighborhood. Differentiate that actual finite slope sum using the independently proved original wave second derivatives, then transfer back by local equality. -/
theorem finiteTargetWave_second_derivative (a : ℝ) (ha : -1<a) (S : Finset ℕ) (c : ℕ → ℝ)
    {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (deriv (finiteTargetWave a ha S c))
      (∑ n∈S,c n*((targetPotential a ha t- jacobi.Bessel.sigma a ha n)*fullWavePhysical a ha n t)) t := by
  have he : deriv (finiteTargetWave a ha S c)=ᶠ[𝓝 t]
      (fun x => ∑ n∈S,c n*deriv (fullWavePhysical a ha n) x) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with x hx
    exact (finiteTargetWave_first_derivative a ha S c hx).deriv
  exact (HasDerivAt.fun_sum (fun n _ =>
    (fullWavePhysical_second_derivative a ha n ht).const_mul (c n))).congr_of_eventuallyEq he

/-- Every arbitrary finite original target combination satisfies the actual printed differential action with its sigma-weighted finite output.
Use: targetOperator_differential identifies this pointwise classical expression with the genuine original full unbounded operator.
Article: jacobi, Theorem 2.1.
Proof: substitute the independently proved true ordinary second-derivative sum. Distribute the unchanged potential across the finite original sum and cancel its actual ODE terms. -/
theorem finiteTargetWave_equation (a : ℝ) (ha : -1<a) (S : Finset ℕ) (c : ℕ → ℝ)
    {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    -deriv (deriv (finiteTargetWave a ha S c)) t+targetPotential a ha t*finiteTargetWave a ha S c t=
      finiteTargetWave a ha S (fun n => c n* jacobi.Bessel.sigma a ha n) t := by
  rw [(finiteTargetWave_second_derivative a ha S c ht).deriv]
  simp only [finiteTargetWave,Finset.mul_sum,← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- The genuine full self-adjoint target operator acts exactly as the original classical Schrodinger expression on every arbitrary finite original target combination.
Use: TargetTestDomain extends this finite-span identity to every compact C2 test, and TargetWeakOperator proves the original differential action distributionally on the full spectral domain.
Article: jacobi, Theorem 2.1.
Proof: the genuine spectral action gives the original sigma-weighted finite state. Its true continuous representative equals the corresponding original finite wave. Away from the two null endpoints the independently proved pointwise classical finite equation identifies this with exactly -v''+V*v, including the actual midpoint. -/
theorem targetOperator_differential (a : ℝ) (ha : -1<a) (S : Finset ℕ) (c : ℕ → ℝ) :
    targetOperator a ha (finiteTargetState a ha S c)=ᵐ[volume]
      (fun t : Interval => -deriv (deriv (finiteTargetWave a ha S c)) (t:ℝ)+
        targetPotential a ha t*finiteTargetWave a ha S c t) := by
  -- Only the singular endpoints are excluded; the actual midpoint is covered by the proved two-sided original C2 equation.
  rw [finiteTargetState_action,finiteTargetState_toLp]
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) volume
    (finiteTargetMap a ha S (fun n => c n* jacobi.Bessel.sigma a ha n)),
    volume.ae_ne (⟨0,by norm_num⟩:Interval),volume.ae_ne (⟨1,by norm_num⟩:Interval)] with t ht h0 h1
  have hti : (t:ℝ)∈Ioo (0:ℝ) 1 :=
    ⟨lt_of_le_of_ne t.property.1 (fun h => h0 (Subtype.ext h.symm)),
      lt_of_le_of_ne t.property.2 (fun h => h1 (Subtype.ext h))⟩
  rw [ht,finiteTargetMap_apply,finiteTargetWave_equation a ha S c hti]

end
end jacobi.GelfandLevitan
