import jacobi.GelfandLevitan.FiniteSystemEquations

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The original finite inverse-system coefficients satisfy their genuine
Darboux differential equation. The actual twice differentiated system,
original Gram Green commutator and genuine finite diagonal derivative
cancel the original residual. All finite-unit and derivative-existence
conditions are discharged by the independently proved original data.
Use: the original finite Gram derivative and spectral commutator have rank-one formulas in finiteDarboux_coefficient_equation.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] realSolution realSlope

/-- The actual original selected-solution pairing with a finite coefficient vector.
Use: the original finite Gram derivative and spectral commutator have rank-one formulas in finiteDarboux_coefficient_equation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteFeatureDot (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) (y : FeatureIndex N→ℝ) : ℝ :=
  ∑ j : FeatureIndex N,realSolution a (finiteFeatureEnergy a ha j) t*y j

/-- The actual original selected-slope pairing with a finite coefficient vector.
Use: the true Gram second derivative and spectral commutator use precisely the same original h' values.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteFeatureSlopeDot (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) (y : FeatureIndex N→ℝ) : ℝ :=
  ∑ j : FeatureIndex N,realSlope a (finiteFeatureEnergy a ha j) t*y j

/-- The original finite spectral diagonal acting on its genuine coefficient vector.
Use: the actual original Gram Green identity computes its commutator with the genuine finite coefficient system.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteFeatureEnergyAction (a : ℝ) (ha : -1<a) (N : ℕ) (y : FeatureIndex N→ℝ) : FeatureIndex N→ℝ :=
  fun i => finiteFeatureEnergy a ha i*y i

/-- The actual original finite system derivative has its genuine original rank-one feature action.
Use: expands the actual once and twice differentiated coefficient equations in the original Darboux residual.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: evaluate the genuine finite coordinate matrix-unit sum; its selected row is precisely the original weighted selected value times the original feature pairing. -/
theorem finiteFeatureSystemSlope_apply (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) (y : FeatureIndex N→ℝ) (i : FeatureIndex N) :
    finiteFeatureSystemSlope a ha N t y i=finiteFeatureWeight a ha i*realSolution a (finiteFeatureEnergy a ha i) t*
      finiteFeatureDot a ha N t y := by
  simp [finiteFeatureSystemSlope,featureMatrixUnit_apply,finiteFeatureDot,Finset.mul_sum,mul_assoc]

/-- The actual original finite system second derivative has its genuine original two rank-one feature actions.
Use: the original actual finite Darboux calculation retains both selected-value and selected-slope terms of B''.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: evaluate the actual original coordinate matrix-unit sum and distribute the two genuine selected-solution product derivatives over the original finite sums. -/
theorem finiteFeatureSystemAcceleration_apply (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) (y : FeatureIndex N→ℝ) (i : FeatureIndex N) :
    finiteFeatureSystemAcceleration a ha N t y i=finiteFeatureWeight a ha i*
      (realSlope a (finiteFeatureEnergy a ha i) t*finiteFeatureDot a ha N t y+
        realSolution a (finiteFeatureEnergy a ha i) t*finiteFeatureSlopeDot a ha N t y) := by
  simp [finiteFeatureSystemAcceleration,featureMatrixUnit_apply,finiteFeatureDot,finiteFeatureSlopeDot,
    Finset.mul_sum,mul_add,add_mul,mul_assoc,Finset.sum_add_distrib]

/-- The genuine original finite diagonal derivative is exactly its original two feature pairings.
Use: the original coefficient Darboux residual cancels by the already proved actual diagonal derivative, fixing the actual finite potential.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: distribute the original finite product derivative sum and commute each pair of real factors. -/
theorem finiteKernelDiagonalSlope_dot (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) :
    finiteKernelDiagonalSlope a ha N t=finiteFeatureDot a ha N t (finiteFeatureCoefficientsSlope a ha N t)+
      finiteFeatureSlopeDot a ha N t (finiteFeatureCoefficients a ha N t) := by
  unfold finiteKernelDiagonalSlope finiteFeatureDot finiteFeatureSlopeDot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The genuine original finite coefficient system has exactly its selected-solution Green commutator with the original energy diagonal.
Use: finiteDarboux_coefficient_equation combines this same original commutator with the actual twice differentiated system, retaining the original finite spectral energies.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: expand the genuine I+C*X action. The original Gram Green identity gives each actual spectral difference, including coincident energies, and the real finite sums collect its two original rank-one boundary factors. -/
theorem finiteFeatureSystem_energy_commutator (a : ℝ) (ha : -1<a) (N : ℕ) (t : HalfInterval) (ht : 0<(t:ℝ))
    (y : FeatureIndex N→ℝ) (i : FeatureIndex N) :
    finiteFeatureSystem a ha N t (finiteFeatureEnergyAction a ha N y) i=
      finiteFeatureEnergy a ha i*finiteFeatureSystem a ha N t y i-
      finiteFeatureWeight a ha i*(realSolution a (finiteFeatureEnergy a ha i) t*finiteFeatureSlopeDot a ha N t y-
        realSlope a (finiteFeatureEnergy a ha i) t*finiteFeatureDot a ha N t y) := by
  -- The commutator is the actual original finite Gram Green identity summed against the same genuine input vector.
  have hsum : finiteFeatureEnergy a ha i*(∑ j : FeatureIndex N,finiteFeatureGram a ha N t i j*y j)-
      (∑ j : FeatureIndex N,finiteFeatureGram a ha N t i j*(finiteFeatureEnergy a ha j*y j))=
      realSolution a (finiteFeatureEnergy a ha i) t*finiteFeatureSlopeDot a ha N t y-
        realSlope a (finiteFeatureEnergy a ha i) t*finiteFeatureDot a ha N t y := by
    unfold finiteFeatureSlopeDot finiteFeatureDot
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    linear_combination y j*finiteFeatureGram_green a ha N t ht i j
  rw [finiteFeatureSystem_apply,finiteFeatureSystem_apply]
  simp only [finiteFeatureEnergyAction]
  linear_combination -(finiteFeatureWeight a ha i)*hsum

/-- Every actual second derivative of the original finite inverse coefficients satisfies the genuine original coefficient Darboux differential equation.
Use: finiteDarboux_coefficient_equation_eventually discharges every finite inverse and second-derivative premise; the original finite kernel then satisfies its actual Darboux PDE.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: apply the actual invertible original finite system to the original Darboux residual. Substitute its independently proved second differentiated coefficient equation, source equation and spectral Gram Green commutator. Both original selected-slope cross terms cancel; the remaining term is exactly the proved finite diagonal derivative. Genuine finite-system injectivity makes the original residual zero. -/
theorem finiteDarboux_coefficient_equation {a d : ℝ} (ha : -1<a) (hd : 0<d) (hds : d<(1/2:ℝ)) (N : ℕ)
    (t : HalfInterval) (hdt : d≤(t:ℝ)) (hu : ∀ x : ℝ,IsUnit (finiteFeatureSystem a ha N x))
    (a2 : FeatureIndex N→ℝ) (ha2 : HasDerivWithinAt (finiteFeatureCoefficientsSlope a ha N) a2 (Icc d (1/2)) (t:ℝ)) :
    ∀ i : FeatureIndex N,a2 i=(potential a t+2*finiteKernelDiagonalSlope a ha N t-finiteFeatureEnergy a ha i)*
      finiteFeatureCoefficients a ha N t i := by
  -- The source matrix acts on the actual original differential residual; every cancellation below comes from a separately proved original identity.
  let α := finiteFeatureCoefficients a ha N t
  let α1 := finiteFeatureCoefficientsSlope a ha N t
  let V := potential a t+2*finiteKernelDiagonalSlope a ha N t
  let θ := a2+finiteFeatureEnergyAction a ha N α-V • α
  have hBθ : finiteFeatureSystem a ha N t θ=0 := by
    funext i
    have h2 := congrArg (fun y : FeatureIndex N→ℝ => y i)
      (finiteFeatureCoefficients_equation_second ha hd hds N ⟨hdt,t.property.2⟩ hu a2 ha2)
    have h0 := congrArg (fun y : FeatureIndex N→ℝ => y i) (finiteFeatureCoefficients_equation a ha N t (hu t))
    have hD := finiteFeatureSystem_energy_commutator a ha N t (hd.trans_le hdt) α i
    have hw := finiteKernelDiagonalSlope_dot a ha N t
    dsimp only [Pi.add_apply,Pi.neg_apply] at h2 h0
    rw [finiteFeatureSystemAcceleration_apply,finiteFeatureSystemSlope_apply] at h2
    change _= -(finiteFeatureWeight a ha i*((potential a t-finiteFeatureEnergy a ha i)*realSolution a (finiteFeatureEnergy a ha i) t)) at h2
    change finiteFeatureSystem a ha N t α i= -(finiteFeatureWeight a ha i*realSolution a (finiteFeatureEnergy a ha i) t) at h0
    change finiteFeatureSystem a ha N t θ i=0
    dsimp only [θ]
    rw [map_sub,map_add,map_smul]
    change finiteFeatureSystem a ha N t a2 i+finiteFeatureSystem a ha N t (finiteFeatureEnergyAction a ha N α) i-
      V*finiteFeatureSystem a ha N t α i=0
    rw [hD,h0]
    dsimp only [α,α1,V] at *
    linear_combination h2+2*finiteFeatureWeight a ha i*realSolution a (finiteFeatureEnergy a ha i) t*hw
  have hθ : θ=0 := (ContinuousLinearMap.isUnit_iff_bijective.mp (hu t)).1 (hBθ.trans (map_zero _).symm)
  intro i
  have hi := congrArg (fun y : FeatureIndex N→ℝ => y i) hθ
  change a2 i+finiteFeatureEnergy a ha i*finiteFeatureCoefficients a ha N t i-
    (potential a t+2*finiteKernelDiagonalSlope a ha N t)*finiteFeatureCoefficients a ha N t i=0 at hi
  linarith

/-- The actual original finite-system coefficient slope satisfies its genuine Darboux differential equation for every sufficiently long original spectral prefix and every positive physical point, with all inverse and second-derivative premises discharged.
Use: finiteKernelDarboux derives the actual original finite transformation-kernel PDE from this genuine original coefficient ODE.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: choose the true positive strip starting at half the original physical point. The genuine original coefficient second derivatives exist by the proved original finite inverse calculus. The actual finite-system units and Gram Green cancellation identify that same derivative with the displayed original Darboux expression. -/
theorem finiteDarboux_coefficient_equation_eventually (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ t : HalfInterval,0<(t:ℝ) →
      HasDerivWithinAt (finiteFeatureCoefficientsSlope a ha N)
        (fun i => (potential a t+2*finiteKernelDiagonalSlope a ha N t-finiteFeatureEnergy a ha i)*
          finiteFeatureCoefficients a ha N t i) (Icc ((t:ℝ)/2) (1/2)) (t:ℝ) := by
  -- The original spectral thresholds discharge every finite inverse and derivative-existence condition before the actual coefficient equation is asserted.
  filter_upwards [finiteFeatureSystem_isUnit a ha,finiteFeatureCoefficients_secondDerivative_exists a ha]
    with N hN hSecond t ht
  have hd : 0<(t:ℝ)/2 := by linarith
  have hds : (t:ℝ)/2<(1/2:ℝ) := by linarith [t.property.2]
  have hdt : (t:ℝ)/2≤(t:ℝ) := by linarith
  obtain ⟨a2,ha2⟩ := hSecond ((t:ℝ)/2) hd t ⟨hdt,t.property.2⟩
  have he := finiteDarboux_coefficient_equation ha hd hds N t hdt hN a2 ha2
  have hval : a2=(fun i => (potential a t+2*finiteKernelDiagonalSlope a ha N t-finiteFeatureEnergy a ha i)*
      finiteFeatureCoefficients a ha N t i) := funext he
  rw [hval] at ha2
  exact ha2

end
end jacobi.GelfandLevitan
