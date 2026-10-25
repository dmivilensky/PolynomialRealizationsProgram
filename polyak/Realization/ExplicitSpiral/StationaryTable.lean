import polyak.Realization.ExplicitSpiral.Physical
import polyak.Realization.Finite
import polyak.Interpolation.FiniteSpan

/-!
Article: the one-atom spectral feasible system is the genuine planar table.
Use: all unchanged interpolation pairs of the explicit initialized spiral.
-/
namespace polyak.Realization.ExplicitSpiral
noncomputable section
open Interpolation Spectral Waves

/-- Article: the sole weighted wave is isometric to the original complex plane. -/
def singletonEmbedding : ℂ →ₗᵢ[ℝ] EuclideanSpace ℂ (Fin 1) where
  toFun z := WithLp.toLp 2 (fun _ => z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' z := by
    change ‖(WithLp.toLp 2 (fun _ : Fin 1 => z) : EuclideanSpace ℂ (Fin 1))‖=‖z‖
    have hh : ‖(WithLp.toLp 2 (fun _ : Fin 1 => z) : EuclideanSpace ℂ (Fin 1))‖^2=‖z‖^2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      simp
    nlinarith [norm_nonneg z,norm_nonneg (WithLp.toLp 2 (fun _ : Fin 1 => z) :
      EuclideanSpace ℂ (Fin 1))]

/-- Article: the exact Dirac spectral constraints imply all planar interpolation pairs. -/
theorem singleton_tableFeasible (c : Frequency) (m : C(Frequency,ℂ)) (C t : ℝ)
    (h : MixtureFeasible ⟨MeasureTheory.Measure.dirac c,by infer_instance⟩ m C t) :
    TableFeasible (modePosition (Waves.z t (Real.arccos c)))
      (modeGradient (Waves.z t (Real.arccos c)) (m c))
      (modeValue (Waves.z t (Real.arccos c)) (m c) C) := by
  let w : Fin 1 → NNReal := fun _ => 1
  let a : Fin 1 → Frequency := fun _ => c
  have hw : ∑ j,w j=1 := by simp [w]
  have hν : finiteSpectrum w a hw=⟨MeasureTheory.Measure.dirac c,by infer_instance⟩ := by
    apply Subtype.ext
    simp [finiteSpectrum,w,a]
  have ht := finite_tableFeasible w a hw (hν.symm ▸ h)
  have hx : finitePosition w a t=fun i => singletonEmbedding
      (modePosition (Waves.z t (Real.arccos c)) i) := by
    funext i
    ext j
    change Real.sqrt (1 : ℝ) • modePosition (Waves.z t (Real.arccos c)) i=
      modePosition (Waves.z t (Real.arccos c)) i
    simp
  have hσ : finiteGradient w a m t=fun i => singletonEmbedding
      (modeGradient (Waves.z t (Real.arccos c)) (m c) i) := by
    funext i
    ext j
    change Real.sqrt (1 : ℝ) • modeGradient (Waves.z t (Real.arccos c)) (m c) i=
      modeGradient (Waves.z t (Real.arccos c)) (m c) i
    simp
  have hv : finiteValue w a m C t=modeValue (Waves.z t (Real.arccos c)) (m c) C := by
    funext i
    cases i <;> simp [finiteValue,w,a,valueMap,Waves.value,modeValue]
  rw [hx,hσ,hv] at ht
  intro i j
  simpa only [datumT_isometry,datumR_isometry] using ht i j

/-- Article: the canonical complex spiral at a positive radial factor. -/
def radialWave (r : ℝ) : ℂ := Waves.z (Real.log r) (Real.arccos (radialCosine r))

/-- Article: the source hyperbolic and value data agree exactly with the spectral spiral. -/
theorem radial_spiral_data {r : ℝ} (hr : 0<r) :
    Spiral.G (Real.log r)=Source.hyperbolic r ∧
    Spiral.cosine (Real.log r)=radialCosine r ∧
    Spiral.gap (Real.log r)=Source.gap r ∧
    Spiral.valueConstant (Real.log r)=physicalValueConstant r := by
  have hG : Spiral.G (Real.log r)=Source.hyperbolic r := by
    simp only [Spiral.G,Real.cosh_eq,Real.exp_neg,Real.exp_log hr,Source.hyperbolic,one_div]
  have hc : Spiral.cosine (Real.log r)=radialCosine r := by
    rw [Spiral.cosine,hG]
    unfold Source.hyperbolic radialCosine
    field_simp
  have hg : Spiral.gap (Real.log r)=Source.gap r := by
    rw [Spiral.gap,hG]
    unfold Source.hyperbolic Source.gap
    field_simp
    ring
  refine ⟨hG,hc,hg,?_⟩
  rw [Spiral.valueConstant,hg,hG,Real.sinh_eq,Real.exp_neg,Real.exp_log hr]
  unfold Source.hyperbolic physicalValueConstant
  field_simp

/-- Article: the canonical radial wave has exactly the source radius and real coordinate. -/
theorem radial_wave_coordinates {r : ℝ} (hr : 0<r) :
    ‖radialWave r‖=r ∧ Complex.normSq (radialWave r)=r^2 ∧
      (radialWave r).re=Source.lambdaReal r := by
  have hn : ‖radialWave r‖=r := by
    have hh := Waves.norm_z_pow (Real.log r) (Real.arccos (radialCosine r)) 1
    simpa only [radialWave,pow_one,Nat.cast_one,one_mul,Real.exp_log hr] using hh
  refine ⟨hn,?_,?_⟩
  · rw [Complex.normSq_eq_norm_sq,hn]
  · have hh := Waves.z_pow_re (Real.log r) (Real.arccos (radialCosine r)) 1
    have hc := radialCosine_mem hr
    have hc' : -1≤radialCosine r ∧ radialCosine r≤1 :=
      ⟨by linarith [hc.1],by linarith [hc.2]⟩
    simp only [pow_one,Nat.cast_one,one_mul,Real.exp_log hr,Real.cos_arccos hc'.1 hc'.2] at hh
    rw [radialWave,hh]
    unfold Source.lambdaReal radialCosine
    ring

/-- Article: the physical multiplier is the spectral Polyak multiplier at the same atom. -/
theorem radial_multiplier {r q : ℝ} (hr : 0<r) (hq : 0<q) :
    multiplier (radialWave r) q=
      polyakMultiplier (Real.log r-Real.log q) (Spiral.atom (Real.log r)) := by
  rw [polyakMultiplier_eq_cosh]
  have hc := (radial_spiral_data hr).2.1
  change _=Complex.cosh (((Real.log r-Real.log q : ℝ) : ℂ)+
    (Real.arccos (Spiral.cosine (Real.log r)) : ℂ)*Complex.I)
  rw [hc,← multiplier_polyak q (Real.log r) (Real.arccos (radialCosine r)) hq]
  simp only [Waves.multiplier,radialWave,multiplier,Complex.ofReal_pow,Complex.ofReal_mul,
    Complex.ofReal_ofNat,Complex.ofReal_zero,sub_zero]

/-- Article: the full stationary table for every positive physical master root. -/
theorem stationary_tableFeasible {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hF : Spiral.spiralPolynomial r q=0) :
    TableFeasible (modePosition (radialWave r))
      (modeGradient (radialWave r) (multiplier (radialWave r) q))
      (modeValue (radialWave r) (multiplier (radialWave r) q) (physicalValueConstant r)) := by
  let t := Real.log r
  have hu : Spiral.twist t=Real.sinh (t-Real.log q) :=
    (Spiral.actual_relation_iff hq t).mpr (by simpa only [t,Real.exp_log hr] using hF)
  have hf : Feasible (t-Real.log q) t (Spiral.spectrum t) (Spiral.valueConstant t) := by
    change FeasibleU (Real.sinh (t-Real.log q)) _ _ _
    rw [← hu]
    exact Spiral.feasibleU t
  have hh := singleton_tableFeasible (Spiral.atom t) (polyakMultiplier (t-Real.log q))
    (Spiral.valueConstant t) t ((mixtureFeasible_polyak_iff _ _ _ _).mpr hf)
  have hc := (radial_spiral_data hr).2.1
  have hC := (radial_spiral_data hr).2.2.2
  have hz : Waves.z t (Real.arccos (Spiral.atom t : ℝ))=radialWave r := by
    change Waves.z (Real.log r) (Real.arccos (Spiral.cosine (Real.log r)))=_
    rw [hc]
    rfl
  rw [hz] at hh
  rw [← radial_multiplier hr hq] at hh
  simpa only [t,hC] using hh

end
end polyak.Realization.ExplicitSpiral
