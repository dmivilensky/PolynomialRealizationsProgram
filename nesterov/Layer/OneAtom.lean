import nesterov.Layer.Coefficients
import nesterov.Layer.RationalScale
import nesterov.Layer.Resonance
import nesterov.Layer.SpreadWitnessRealization
import nesterov.TwoStep.SequenceCeiling

/-! The one-atom lower bound in the layer, with its literal initialized
real witness and the weaker factor Lambda_+/2. -/
namespace nesterov.TwoStep
noncomputable section
open Spectral Phase Filter Set
open scoped Topology NNReal

theorem mixed_test_reserve (q : Momentum.Tuning) {μ L r : ℝ}
    (hμL : μ<L) (hr : 0<r) {K : ℕ} (hK : 3≤K)
    (him : 0<(Quadratic.characteristic q.beta q.tau q.stepSize μ (circle r (2*Real.pi/K))*
      star (Quadratic.characteristic q.beta q.tau q.stepSize L (circle r (2*Real.pi/K)))).im)
    (hH : ((1-circle 1 (2*Real.pi/K))*
      Quadratic.characteristic q.beta q.tau q.stepSize μ (circle r (2*Real.pi/K))*
      star (Quadratic.characteristic q.beta q.tau q.stepSize L (circle r (2*Real.pi/K)))).re≤0) :
    |(0:ℝ)|<meanG (singletonSpectrum (frequency (2*Real.pi/K)))
      ((Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L (Real.log r)) := by
  let ω := 2*Real.pi/K
  let a := (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne').symbolPair μ L (Real.log r)
  have hω : ω∈Ioo (0:ℝ) Real.pi := by
    simpa [ω,polyak.General.Regions.rationalAngle] using
      polyak.General.Regions.rationalAngle_mem (j:=1) (k:=K) le_rfl (by omega)
  have hf := momentum_factor (β:=q.beta) (τ:=q.tau) hμL q.step_pos.ne'
    (Real.log r) (frequency ω)
  rw [arccos_frequency ⟨hω.1.le,hω.2.le⟩,wave_log_radius hr] at hf
  let B := Quadratic.characteristic q.beta q.tau q.stepSize μ (circle r ω)*
    star (Quadratic.characteristic q.beta q.tau q.stepSize L (circle r ω))
  let k : ℝ := 4/(q.stepSize^2*(L-μ)^2)
  have hk : 0<k := div_pos (by norm_num)
    (mul_pos (sq_pos_of_pos q.step_pos) (sq_pos_of_pos (sub_pos.mpr hμL)))
  have hf' : (g a (frequency ω):ℂ)-2*Complex.I*skew a (frequency ω)= -(k:ℂ)*B := by
    convert hf using 1
    dsimp [B,k]
    ring
  have hs : 0<skew a (frequency ω) := by
    have hi := congrArg Complex.im hf'
    have hie : -2*skew a (frequency ω)= -k*B.im := by simpa using hi
    have hprod : 0<B.im := him
    nlinarith [mul_pos hk hprod]
  have hfeas := (singleton_feasible_iff a (Real.log r) 0 (frequency ω)).mp
    (mixed_test q hμL hr hK him hH)
  have hg : 0<g a (frequency ω) := by
    have hg0 : 0≤g a (frequency ω) := by simpa only [abs_zero] using hfeas.1
    by_contra hn
    have hgz : g a (frequency ω)=0 := by linarith
    have hl := (hfeas.2 1 le_rfl).1
    simp [lagA,lagB,hgz,arccos_frequency ⟨hω.1.le,hω.2.le⟩] at hl
    have hsp := mul_pos (mul_pos (by norm_num : (0:ℝ)<2) hs)
      (Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2)
    linarith
  simpa only [singleton_meanG,abs_zero] using hg

namespace Scaling
variable {A : Type*} {l : Filter A} {θ y : ℝ} (F : Scaling A l θ y (1/2))

private theorem mixedBracket_rescale {ε s θ τ c ξ : ℝ} (hs : s^2=ε) (hsp : s≠0) :
    s*(θ-2*c)+c^2*(1+τ)*(ε*s)+2*τ*(1-c*ε)*(ξ/s)=
      mixedBracket (1-θ*ε) τ (1-c*ε) ξ/s := by
  rw [←hs]
  unfold mixedBracket
  field_simp
  ring

theorem mixedBracket_layer_tendsto {φ₀ : ℝ} {ξ : A→ℝ} (c : ℝ)
    (hξ : Tendsto (fun a=>ξ a/Real.sqrt (F.epsilon a)) l (𝓝 φ₀)) :
    Tendsto (fun a=>mixedBracket (F.tuning a).beta (F.tuning a).tau
      (1-c*F.epsilon a) (ξ a)/Real.sqrt (F.epsilon a)) l (𝓝 φ₀) := by
  have hrad : Tendsto (fun a=>1-c*F.epsilon a) l (𝓝 1) := by
    simpa only [mul_zero,sub_zero] using
      (tendsto_const_nhds (x:=(1:ℝ))).sub (F.epsilon_zero.const_mul c)
  have ht := ((F.sqrt_epsilon_tendsto.mul
    (F.theta_tendsto.sub_const (2*c))).add
      (((F.tau_tendsto.const_add 1).const_mul (c^2)).mul
        (F.epsilon_zero.mul F.sqrt_epsilon_tendsto))).add
      (((F.tau_tendsto.const_mul 2).mul hrad).mul hξ)
  norm_num only [zero_mul,mul_zero,zero_add,one_mul] at ht
  apply ht.congr'
  filter_upwards [F.beta_eq,F.epsilon_pos] with a hb he
  change Real.sqrt (F.epsilon a)*(F.thetaAt a-2*c)+
    c^2*(1+(F.tuning a).tau)*(F.epsilon a*Real.sqrt (F.epsilon a))+
      2*(F.tuning a).tau*(1-c*F.epsilon a)*(ξ a/Real.sqrt (F.epsilon a))=_
  rw [hb]
  exact mixedBracket_rescale (Real.sq_sqrt he.le) (Real.sqrt_pos.mpr he).ne'

/-- Remark one-layer: the singleton spectrum really is feasible at the
literal radius 1-c epsilon, and it has one real initialized all-time witness. -/
theorem layer_one_atom {B c : ℝ} (hy2 : y<2) (hBp : 0<B)
    (hB : Tendsto F.layerDeficit l (𝓝 B))
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1)
    (hc : max (Layer.Lambda θ y B) 0/2<c) :
    ∀ᶠ a in l,
      3≤F.layerPeriod B a ∧
      Feasible ((Momentum.method (F.tuning a).beta (F.tuning a).tau
        (F.tuning a).stepSize (F.tuning a).step_pos.ne').symbolPair (F.epsilon a^2) 1
          (Real.log (1-c*F.epsilon a))) (Real.log (1-c*F.epsilon a))
        (singletonSpectrum (frequency (2*Real.pi/F.layerPeriod B a))) 0 ∧
      |(0:ℝ)|<meanG (singletonSpectrum (frequency (2*Real.pi/F.layerPeriod B a)))
        ((Momentum.method (F.tuning a).beta (F.tuning a).tau
          (F.tuning a).stepSize (F.tuning a).step_pos.ne').symbolPair (F.epsilon a^2) 1
            (Real.log (1-c*F.epsilon a))) ∧
      RestLowerWitness (F.tuning a) (F.epsilon a^2) 1 (1-c*F.epsilon a) 3 ∧
      1-c*F.epsilon a≤Momentum.momentumRestRate (F.tuning a).beta (F.tuning a).tau
        (F.tuning a).stepSize (F.tuning a).step_pos.ne' (F.epsilon a^2) 1 := by
  let φ : ℝ := B*y/(2-y)
  have hφ : 0<φ := div_pos (mul_pos hBp F.step_pos) (by linarith)
  let ξ : A→ℝ := fun a=>Layer.rationalXi φ (Real.sqrt (F.epsilon a))
  have hx : Tendsto (fun a=>ξ a/Real.sqrt (F.epsilon a)) l (𝓝 φ) :=
    (Layer.rationalXi_scaled_tendsto hφ).comp F.sqrt_epsilon_tendstoGT
  have hpoly := (F.layer_mixed_tendsto c hB hx).eventually
    (eventually_lt_nhds (Layer.mixedPolynomial_min_neg F.step_pos hy2 hBp hc))
  have hbracket := (F.mixedBracket_layer_tendsto c hx).eventually (eventually_gt_nhds hφ)
  have hK := F.sqrt_epsilon_tendstoGT.eventually (Layer.rationalPeriod_eventually_ge_three hφ)
  have hrad : Tendsto (fun a=>1-c*F.epsilon a) l (𝓝 1) := by
    simpa only [mul_zero,sub_zero] using
      (tendsto_const_nhds (x:=(1:ℝ))).sub (F.epsilon_zero.const_mul c)
  filter_upwards [hpoly,hbracket,hK,F.epsilon_pos,F.beta_eq,hstable,
    F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    hrad.eventually (eventually_gt_nhds (by norm_num : (0:ℝ)<1))]
      with a hpoly hbracket hK he hb hs he1 hr
  let q := F.tuning a
  let r := 1-c*F.epsilon a
  let ω := 2*Real.pi/F.layerPeriod B a
  have hμ : 0<F.epsilon a^2 := sq_pos_of_pos he
  have hμL : F.epsilon a^2<1 := by nlinarith
  have hω : ω∈Ioo (0:ℝ) Real.pi := Layer.rationalAngle_mem hK
  have hξeq : ξ a=1-Real.cos ω := rfl
  have hξpos : 0<ξ a := by
    rw [hξeq]
    apply sub_pos.mpr
    simpa only [Real.cos_zero] using Real.cos_lt_cos_of_nonneg_of_le_pi
      (by norm_num : (0:ℝ)≤0) hω.2.le hω.1
  have hmul : Real.sqrt (F.epsilon a)*(ξ a/Real.sqrt (F.epsilon a))=ξ a := by
    field_simp [(Real.sqrt_pos.mpr he).ne']
  have hmixed : mixedPolynomial q.beta q.tau (q.stepSize*F.epsilon a^2) q.stepSize r (ξ a)<0 := by
    rw [hmul] at hpoly
    have hneg := (div_lt_iff₀ he).mp hpoly
    simp only [zero_mul] at hneg
    rw [hb,mixedPolynomial_coefficients]
    exact hneg
  have him : 0<(Quadratic.characteristic q.beta q.tau q.stepSize (F.epsilon a^2) (circle r ω)*
      star (Quadratic.characteristic q.beta q.tau q.stepSize 1 (circle r ω))).im := by
    have hbpos : 0<mixedBracket q.beta q.tau r (ξ a) :=
      (div_pos_iff_of_pos_right (Real.sqrt_pos.mpr he)).mp hbracket
    have hpos := mul_pos (mul_pos (mul_pos
      (sub_pos.mpr (mul_lt_mul_of_pos_left hμL q.step_pos)) hr)
        (Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2)) hbpos
    have hi := cross_im_circle q.beta q.tau (q.stepSize*F.epsilon a^2) q.stepSize r ω
    rw [hξeq] at hpos
    have hunit : 0<(Quadratic.characteristic q.beta q.tau 1 (q.stepSize*F.epsilon a^2)
        (circle r ω)*star (Quadratic.characteristic q.beta q.tau 1 q.stepSize (circle r ω))).im := by
      rw [hi]
      simpa only [mul_one,r] using hpos
    simpa only [Quadratic.characteristic,one_mul,mul_one] using hunit
  have hH : ((1-circle 1 ω)*
      Quadratic.characteristic q.beta q.tau q.stepSize (F.epsilon a^2) (circle r ω)*
      star (Quadratic.characteristic q.beta q.tau q.stepSize 1 (circle r ω))).re≤0 := by
    have hneg := mul_neg_of_pos_of_neg hξpos hmixed
    have hi := mixed_symbol q.beta q.tau (q.stepSize*F.epsilon a^2) q.stepSize r ω
    have hh : ((1-circle 1 ω)*Quadratic.characteristic q.beta q.tau 1
        (q.stepSize*F.epsilon a^2) (circle r ω)*
        star (Quadratic.characteristic q.beta q.tau 1 q.stepSize (circle r ω))).re<0 := by
      rw [hi]
      exact hneg
    simpa only [Quadratic.characteristic,one_mul,mul_one] using hh.le
  have hf := mixed_test q (by linarith : F.epsilon a^2<1) hr hK him hH
  have hres := mixed_test_reserve q (by linarith : F.epsilon a^2<1) hr hK him hH
  refine ⟨hK,hf,hres,?_,?_⟩
  · exact finite_spectrum_rest_witness q hμ hμL hs hr
      (fun _ : Fin 1=>(1:ℝ≥0)) (fun _=>frequency ω) (by simp) hf hres
  · exact rest_rate_ge_of_finite_spectrum q hμ hμL hs hr
      (fun _ : Fin 1=>(1:ℝ≥0)) (fun _=>frequency ω) (by simp) hf hres

theorem layer_one_atom_coefficient_le {B c : ℝ} (hy2 : y<2) (hBp : 0<B)
    (hB : Tendsto F.layerDeficit l (𝓝 B))
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1)
    (hc : max (Layer.Lambda θ y B) 0/2<c) :
    ∀ᶠ a in l,F.restCoefficientAt a≤c := by
  filter_upwards [F.layer_one_atom hy2 hBp hB hstable hc,F.epsilon_pos] with a ha he
  unfold restCoefficientAt
  apply (div_le_iff₀ he).mpr
  linarith [ha.2.2.2.2]

end Scaling
end
end nesterov.TwoStep
