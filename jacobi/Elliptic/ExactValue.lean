import jacobi.Elliptic.TurningRescale
import jacobi.Elliptic.StrictImprovement

/-!
Article: jacobi, Theorem D.5.
The actual optimizer's mass, energy and second moment are expressed in the
unit-interval quadratures. Their exact algebra eliminates the Euler scale
and gives the printed unique ratio parameter and the value M^(3/2)*Xi(t).
The attainer comes from the proved direct method, with actual KKT, ODE,
turning geometry and Jacobian identities discharged beforehand.
Source: the final normalization in the article's proof of elliptic calibration.
Use: gives the normalized attained second-moment minimum after the ratio parameter is selected.
-/
namespace jacobi.Elliptic
noncomputable section
open MeasureTheory Real Filter Set jacobi.Variational
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The article's exact elliptic energy coefficient, using its positive square-root parameter branch.
Use: gives the normalized attained second-moment minimum after the ratio parameter is selected.
Article: jacobi, Theorem D.5.
-/
def Xi (t : ℝ) : ℝ := i3 t 0/(sqrt t*(i2 t 0)^(3/2:ℝ))

/-- The actual elliptic optimizer has the three printed rescaled quadrature values.
Use: supplies exact mass and spectral ratio and eliminates the scale in the energy minimum.
Article: jacobi, Theorem D.5.
Proof: substitute the actual turning parameter into the proved original
mass, energy and spectral-moment quadratures, then apply their exact unit-interval rescalings. -/
theorem euler_quadratures_rescaled (m : Density) (hm : 0<m.mass) (hs : SymmetricDecreasing m.value)
    {μ l t : ℝ} (hμ : 0<μ) (hl : 0<l) (ht : t∈Ioo (0:ℝ) 1)
    (he : m.value=ᵐ[volume] eulerDensity m μ l)
    (hY : eulerState m μ l 0=(t⁻¹)^2) (hσ : eulerShift μ l=(t⁻¹)^2-(t⁻¹)^3) :
    m.mass=(4/9:ℝ)*(eulerScale μ)^2*(t⁻¹)^3*i2 t 0 ∧
      observe m .second=(32/243:ℝ)*(eulerScale μ)^4*(t⁻¹)^6*kappa t ∧
      m.energy=(8/27:ℝ)*(eulerScale μ)^3*(t⁻¹)^5*i3 t 0 := by
  -- All three identities concern one original actual density and its same actual parameter t.
  obtain ⟨hM,hE⟩ := euler_mass_energy_quadratures m hm hs hμ hl he
  have hG := euler_second_quadrature m hm hs hμ hl he
  rw [hY,hσ,(state_integrals_rescale ht).1] at hM
  rw [hY,hσ,(state_integrals_rescale ht).2] at hE
  rw [hY,hσ,state_mixed_rescale ht] at hG
  exact ⟨by nlinarith [hM],by nlinarith [hG],by nlinarith [hE]⟩

/-- The exact Euler amplitude disappears from the actual moment-to-mass-square ratio.
Use: the proved unique inverse of r identifies the optimizer's t with the prescribed threshold parameter.
Article: jacobi, Theorem D.5.
Proof: substitute the literal mass and second-moment quadratures and cancel their positive common amplitude. -/
theorem quadrature_ratio {a t M T : ℝ} (ha : 0<a) (ht : t∈Ioo (0:ℝ) 1)
    (hM : M=(4/9:ℝ)*a^2*(t⁻¹)^3*i2 t 0)
    (hT : T=(32/243:ℝ)*a^4*(t⁻¹)^6*kappa t) : T/M^2=ratio t := by
  have htpos := ht.1
  have hi : 0 < i2 t 0 := i2_pos ⟨ht.1.le,ht.2.le⟩ (by norm_num)
  rw [hM,hT,ratio]
  field_simp [ha.ne',ht.1.ne',hi.ne']
  ring

/-- The exact mass normalization turns the genuine energy quadrature into M^(3/2)*Xi(t).
Use: gives the precise attained value after the unique elliptic ratio parameter is fixed.
Article: jacobi, Theorem D.5.
Proof: evaluate sqrt(M) from the positive explicit mass quadrature. The
real 3/2 powers are value times square root, so only exact polynomial
and positive square-root identities remain after scalar cancellation. -/
theorem quadrature_energy {a t M E : ℝ} (ha : 0<a) (ht : t∈Ioo (0:ℝ) 1)
    (hM : M=(4/9:ℝ)*a^2*(t⁻¹)^3*i2 t 0)
    (hE : E=(8/27:ℝ)*a^3*(t⁻¹)^5*i3 t 0) : E=M^(3/2:ℝ)*Xi t := by
  -- Positive square roots fix every fractional-power branch in the printed minimum.
  have htpos := ht.1
  have hi : 0 < i2 t 0 := i2_pos ⟨ht.1.le,ht.2.le⟩ (by norm_num)
  have hMp : 0<M := by rw [hM]; positivity
  have hst := Real.sq_sqrt ht.1.le
  have hsi := Real.sq_sqrt hi.le
  let root := (2/3:ℝ)*a*(t⁻¹)^2*sqrt t*sqrt (i2 t 0)
  have hrpos : 0<root := by dsimp only [root]; positivity
  have hr : root^2=M := by
    rw [hM]
    dsimp only [root]
    simp only [mul_pow,hst,hsi]
    field_simp [ht.1.ne']
    ring
  have hsM : sqrt M=root := by rw [← hr,Real.sqrt_sq hrpos.le]
  rw [hE,rpow_three_halves hMp.le,hsM,Xi,rpow_three_halves hi.le,hM]
  dsimp only [root]
  field_simp [(sqrt_pos.mpr ht.1).ne',(sqrt_pos.mpr hi).ne']
  nlinarith [hst,hsi]

/-- Every actual elliptic minimizer has the unique ratio parameter and its exact printed energy value.
Use: identifies the attained infimum from the direct method with the article's explicit elliptic calibration.
Article: jacobi, Theorem D.5.
Proof: actual mass saturation, KKT and profile geometry construct the
turning parameter. The proved Jacobian and rescaled quadratures give its
ratio and energy; all original variational constraints remain actual equalities. -/
theorem elliptic_optimizer_exact {M T : ℝ} (hT : 0<T) (hregime : 2*M^2<5*T)
    (m : Density) (hm : 0<m.mass) (hs : SymmetricDecreasing m.value)
    (hmM : m.mass≤M) (hmT : T≤observe m .second)
    (hmin : m.cost=relaxedInfimum {Observation.second} M (fun _ => T)) :
    ∃ t : ℝ,t∈Ioo (0:ℝ) 1 ∧ ratio t=T/M^2 ∧ m.mass=M ∧
      observe m .second=T ∧ m.energy=M^(3/2:ℝ)*Xi t := by
  -- The turning parameter and all three integral formulas concern the same attained actual minimizer.
  obtain ⟨hmass,hG,μ,l,t,a,hμ,hl,ht,_ha,he,hY,hσ,_hzero,_hcore,_hslope⟩ :=
    elliptic_optimizer_geometry hT hregime m hm hs hmM hmT hmin
  obtain ⟨hM,hTq,hE⟩ := euler_quadratures_rescaled m hm hs hμ hl ht he hY hσ
  rw [hmass] at hM
  rw [hG] at hTq
  exact ⟨t,ht,(quadrature_ratio (eulerScale_pos hμ) ht hM hTq).symm,hmass,hG,
    quadrature_energy (eulerScale_pos hμ) ht hM hE⟩

/-- The complete elliptic calibration: unique parameter, exact attained infimum, and an actual radial optimizer.
Use: closes the root-free second-moment calibration throughout the strict elliptic regime.
Article: jacobi, Theorem D.5.
Proof: the direct method supplies an actual radial minimizer. The complete
Euler, phase and quadrature chain evaluates its genuine energy. Strict
monotonicity of the already proved literal ratio makes its parameter unique. -/
theorem elliptic_calibration {M T : ℝ} (hM : 0<M) (hT : 0<T)
    (hregime : 2*M^2<5*T) (hsub : T<M^2) :
    ∃ t : ℝ,t∈Ioo (0:ℝ) 1 ∧ ratio t=T/M^2 ∧
      (∀ u : ℝ,u∈Ioo (0:ℝ) 1 → ratio u=T/M^2 → u=t) ∧
      relaxedInfimum {Observation.second} M (fun _ => T)=ENNReal.ofReal (M^(3/2:ℝ)*Xi t) ∧
      ∃ m : Density,SymmetricDecreasing m.value ∧ m.mass=M ∧ observe m .second=T ∧
        m.energy=M^(3/2:ℝ)*Xi t ∧ m.cost=relaxedInfimum {Observation.second} M (fun _ => T) := by
  -- Existence is unconditional at the stated actual subcritical thresholds.
  obtain ⟨m,hs,hm,hmM,hG,hmin⟩ := second_minimizer_exists hM hT hsub
  obtain ⟨t,ht,hratio,hmass,hmoment,hE⟩ := elliptic_optimizer_exact hT hregime m hm hs hmM hG.ge hmin
  refine ⟨t,ht,hratio,?_,?_,m,hs,hmass,hmoment,hE,hmin⟩
  · intro u hu huratio
    exact ratio_strictAntiOn.injOn hu ht (huratio.trans hratio.symm)
  · rw [← hmin]
    exact congrArg ENNReal.ofReal hE

/-- The literal edge-spectrum elliptic theorem: unique parameter, exact attained minimum and strict Young improvement.
Use: specializes the general proved calibration to the article's actual spectral thresholds, with no additional positivity or feasibility premises.
Article: jacobi, Theorem D.5.
Proof: positivity and summability of the actual edge spectrum give the
strictly subcritical moment threshold. Its singleton admissible set agrees
with the general calibration's constant threshold. Combine its actual
attainer and exact value with the already proved strict Young comparison. -/
theorem elliptic_edge_calibration (Λ : EdgeSpectrum) (hregime : 2*Λ.mass^2<5*Λ.second) :
    ∃ t : ℝ,t∈Ioo (0:ℝ) 1 ∧ ratio t=Λ.second/Λ.mass^2 ∧
      (∀ u : ℝ,u∈Ioo (0:ℝ) 1 → ratio u=Λ.second/Λ.mass^2 → u=t) ∧
      relaxedInfimum {Observation.second} Λ.mass (threshold Λ)=
        ENNReal.ofReal (Λ.mass^(3/2:ℝ)*Xi t) ∧
      ENNReal.ofReal (jacobi.Young.youngValue Λ.second)<
        ENNReal.ofReal (Λ.mass^(3/2:ℝ)*Xi t) ∧
      ∃ m : Density,SymmetricDecreasing m.value ∧ m.mass=Λ.mass ∧ observe m .second=Λ.second ∧
        m.energy=Λ.mass^(3/2:ℝ)*Xi t ∧
        m.cost=relaxedInfimum {Observation.second} Λ.mass (threshold Λ) := by
  -- The source's own edge data discharge every input of the general attained calibration.
  have hsum := jacobi.Continuum.summable_powers Λ.summable (fun n => (Λ.positive n).le) (by decide : 0<2)
  have hT : 0<Λ.second := (sq_pos_of_pos (Λ.positive 0)).trans_le
    (hsum.le_tsum 0 (fun n _ => sq_nonneg (Λ.value n)))
  have hproblem : relaxedInfimum {Observation.second} Λ.mass (threshold Λ)=
      relaxedInfimum {Observation.second} Λ.mass (fun _ => Λ.second) := by
    unfold relaxedInfimum
    congr 1
    ext m
    simp [threshold]
  obtain ⟨t,ht,hr,hu,hvalue,m,hs,hm,hG,hE,hcost⟩ :=
    elliptic_calibration Λ.mass_pos hT hregime Λ.second_lt_mass_sq
  refine ⟨t,ht,hr,hu,by rw [hproblem,hvalue],?_,m,hs,hm,hG,hE,by rwa [hproblem]⟩
  rw [← hvalue]
  exact second_infimum_strict_young Λ.mass_pos hT Λ.second_lt_mass_sq hregime

end
end jacobi.Elliptic
