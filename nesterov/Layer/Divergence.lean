import nesterov.Layer.Resonance
import Mathlib.Topology.Instances.EReal.Lemmas

/-! The full liminf form of layer divergence, without assuming a limit or
boundedness of the positive deficit. -/
namespace nesterov.TwoStep.Scaling
noncomputable section
open Filter Set
open scoped Topology
variable {A : Type*} {l : Filter A} {θ y : ℝ} (F : Scaling A l θ y (1/2))

/-- A fixed lower bound on the deficit suffices: monotonicity of its linear
term gives one rational period even for arbitrarily large deficits. -/
theorem layer_divergence_above {B : ℝ} (hy2 : y<2)
    (hBA : Layer.Astar θ y<B)
    (hB : ∀ᶠ a in l,B≤F.layerDeficit a)
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) :
    Tendsto (fun a=>(F.layerPeriod B a:ℝ)*Real.sqrt (Real.sqrt (F.epsilon a))) l
      (𝓝 (Real.pi*Real.sqrt (2/(B*y/(2-y))))) ∧
      ∀ᶠ a in l,ResonanceWitness (F.tuning a) (F.epsilon a^2) 1 (F.layerPeriod B a) := by
  have hBp : 0<B := (Layer.Astar_pos F.theta_pos F.step_pos hy2).trans hBA
  let φ : ℝ := B*y/(2-y)
  let ζ : A→ℝ := fun a=>Layer.rationalXi φ (Real.sqrt (F.epsilon a))/Real.sqrt (F.epsilon a)
  let U : A→ℝ := fun a=> -4*(F.tuning a).stepSize*B+
    Real.sqrt (F.epsilon a)*F.layerError 0 1 a
  have hφ : 0<φ := div_pos (mul_pos hBp F.step_pos) (by linarith)
  have hζ : Tendsto ζ l (𝓝 φ) :=
    (Layer.rationalXi_scaled_tendsto hφ).comp F.sqrt_epsilon_tendstoGT
  have hU : Tendsto U l (𝓝 (-4*y*B)) := by
    have ht := ((F.step_tendsto.const_mul (-4)).mul_const B).add
      (F.sqrt_epsilon_tendsto.mul (F.layerError_tendsto 0 1))
    simpa only [zero_mul,add_zero] using ht
  have hp3 : Tendsto (fun a=>scaledP3 (F.epsilon a) 0 (F.thetaAt a)
      (F.tuning a).stepSize (F.tuning a).tau) l (𝓝 (2*(2-y))) := by
    have hv : 4*(1-(1/2)*y)=2*(2-y) := by ring
    simpa only [hv] using F.P3_tendsto 0
  have ht := ((F.P1_div_tendsto 0).add (hU.mul hζ)).add (hp3.mul (hζ.pow 2))
  have hv : 2*y*(θ-3*0)+(-4*y*B)*φ+2*(2-y)*φ^2=Layer.polynomial θ y 0 B φ := by
    unfold Layer.polynomial;ring
  rw [hv] at ht
  have hneg : Layer.polynomial θ y 0 B φ<0 := by
    rw [Layer.polynomial_minimum hy2]
    have hLambda := Layer.Lambda_neg_of_Astar_lt F.theta_pos F.step_pos hy2 hBA
    rw [Layer.Lambda,max_eq_left hBp.le] at hLambda
    have hh : θ*(2-y)<y*B^2 :=
      (lt_div_iff₀ (show 0<2-y by linarith)).mp (by linarith : θ<y*B^2/(2-y))
    exact mul_neg_of_pos_of_neg (div_pos (mul_pos (by norm_num) F.step_pos) (by linarith))
      (by nlinarith)
  have hK := F.sqrt_epsilon_tendstoGT.eventually (Layer.rationalPeriod_eventually_ge_three hφ)
  constructor
  · exact (Layer.rationalPeriod_scaled_tendsto hφ).comp F.sqrt_epsilon_tendstoGT
  · filter_upwards [ht.eventually (eventually_lt_nhds hneg),hK,hB,F.epsilon_pos,F.beta_eq,
      F.P2_layer_exact 0,F.layer_tail_exact 0,hstable,
      F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
      with a hn hK hB he hb hP2 hTail hs he1
    have hζpos : 0≤ζ a := div_nonneg
      (sub_nonneg.mpr (Real.cos_le_one _)) (Real.sqrt_nonneg _)
    have hP2le : scaledP2 (F.epsilon a) 0 (F.thetaAt a) (F.tuning a).stepSize
        (F.tuning a).tau/Real.sqrt (F.epsilon a)≤U a := by
      rw [hP2]
      have hm := mul_le_mul_of_nonneg_left hB
        (mul_nonneg (show (0:ℝ)≤4 by norm_num) (F.tuning a).step_pos.le)
      dsimp [U]
      linarith
    have hNormalized : scaledTail (F.epsilon a) 0 (F.thetaAt a) (F.tuning a).stepSize
        (F.tuning a).tau (Real.sqrt (F.epsilon a)*ζ a)/F.epsilon a<0 := by
      rw [hTail]
      have hm := mul_le_mul_of_nonneg_right hP2le hζpos
      linarith
    have hmul : Real.sqrt (F.epsilon a)*ζ a=Layer.rationalXi φ (Real.sqrt (F.epsilon a)) := by
      dsimp [ζ]
      field_simp [(Real.sqrt_pos.mpr he).ne']
    rw [hmul,scaledTail_zero] at hNormalized
    have hneg' := (div_lt_iff₀ he).mp hNormalized
    simp only [zero_mul] at hneg'
    apply resonanceWitness_of_negative (F.tuning a) (sq_pos_of_pos he) (by nlinarith) hs hK
    simpa only [layerPeriod,φ,Layer.rationalXi,Layer.rationalAngle,mul_one,hb] using hneg'

/-- The original liminf form, including unbounded and oscillating deficits.
No countability or convergence hypothesis is added to the parameter filter. -/
theorem layer_divergence_of_liminf (hy2 : y<2)
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1)
    (hlim : (Layer.Astar θ y:EReal)<liminf (fun a=>(F.layerDeficit a:EReal)) l) :
    ∀ᶠ a in l,∃ K : ℕ,ResonanceWitness (F.tuning a) (F.epsilon a^2) 1 K := by
  obtain ⟨B,hB,hBlim⟩ := EReal.exists_between_coe_real hlim
  have hBA : Layer.Astar θ y<B := EReal.coe_lt_coe_iff.mp hB
  have hevent : ∀ᶠ a in l,B≤F.layerDeficit a :=
    (eventually_lt_of_lt_liminf hBlim).mono fun _ ha=>(EReal.coe_lt_coe_iff.mp ha).le
  exact (F.layer_divergence_above hy2 hBA hevent hstable).2.mono fun a ha=>⟨_,ha⟩

end
end nesterov.TwoStep.Scaling
