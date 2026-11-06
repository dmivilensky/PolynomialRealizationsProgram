import nesterov.Layer.Coefficients
import nesterov.Layer.RationalScale
import nesterov.TwoStep.Band

/-! The layer's divergent real periodic witnesses, with the same rational
period in the strict phase inequality and the actual initialized orbit. -/
namespace nesterov.Layer
noncomputable section

theorem Lambda_neg_of_Astar_lt {θ y B : ℝ}
    (hθ : 0<θ) (hy : 0<y) (hy2 : y<2) (hB : Astar θ y<B) :
    Lambda θ y B<0 := by
  have hs := Astar_sq hθ hy hy2
  have hp := Astar_pos hθ hy hy2
  have hBp : 0<B := hp.trans hB
  have hsq : Astar θ y^2<B^2 := by nlinarith
  have hm := mul_lt_mul_of_pos_left hsq hy
  have he : y*Astar θ y^2=θ*(2-y) := by rw [hs];field_simp
  rw [he] at hm
  have hd := (lt_div_iff₀ (show 0<2-y by linarith)).mpr hm
  rw [Lambda,max_eq_left hBp.le]
  linarith

end
end nesterov.Layer

namespace nesterov.TwoStep
noncomputable section
open Filter Set
open scoped Topology

theorem scaledTail_zero (ε θ y τ ξ : ℝ) :
    scaledTail ε 0 θ y τ ξ=Ltau (1-θ*ε) τ (y*ε^2) y ξ := by
  simp only [scaledTail,scaledP1,scaledP2,scaledP3,P1,P2,P3,E0,E1,E2,
    Quadratic.S,Quadratic.Q,Ltau,A0,A1,A2]
  ring

def ResonanceWitness (q : Momentum.Tuning) (μ L : ℝ) (K : ℕ) : Prop :=
  3≤K ∧ Phase.momentumAngle q μ L (2*Real.pi/K)<Real.pi/K ∧
    HasPeriodicRestWitness q μ L K ∧
      1<Momentum.momentumRestRate q.beta q.tau q.stepSize q.step_pos.ne' μ L

theorem resonanceWitness_of_negative (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L) {K : ℕ} (hK : 3≤K)
    (hneg : Ltau q.beta q.tau (q.stepSize*μ) (q.stepSize*L)
      (1-Real.cos (2*Real.pi/K))<0) : ResonanceWitness q μ L K := by
  have hangle : 2*Real.pi/K∈Ioo (0:ℝ) Real.pi := by
    simpa [polyak.General.Regions.rationalAngle] using
      polyak.General.Regions.rationalAngle_mem (j:=1) (k:=K) le_rfl (by omega)
  have hp := (stable_Ltau_phase_sign q hμ hμL hs ⟨hangle.1,hangle.2.le⟩).2.2.mp hneg
  rw [show 2*Real.pi/(K:ℝ)/2=Real.pi/K by ring] at hp
  exact ⟨hK,hp,negative_Ltau_periodic_rest q hμ hμL hs hK hneg,
    negative_Ltau_restRate q hμ hμL hs hK hneg⟩

namespace Scaling
variable {A : Type*} {l : Filter A} {θ y : ℝ} (F : Scaling A l θ y (1/2))

theorem sqrt_epsilon_tendstoGT :
    Tendsto (fun a=>Real.sqrt (F.epsilon a)) l (𝓝[>] (0:ℝ)) := by
  exact tendsto_nhdsWithin_iff.mpr ⟨F.sqrt_epsilon_tendsto,
    F.epsilon_pos.mono fun _ h=>Real.sqrt_pos.mpr h⟩

def layerPeriod (B : ℝ) (a : A) : ℕ :=
  Layer.rationalPeriod (B*y/(2-y)) (Real.sqrt (F.epsilon a))

/-- A finite supercritical deficit gives the exact source period scale and
one genuine three-dimensional periodic-from-rest witness at that period. -/
theorem layer_divergence_finite {B : ℝ} (hy2 : y<2)
    (hB : Tendsto F.layerDeficit l (𝓝 B)) (hBA : Layer.Astar θ y<B)
    (hstable : ∀ᶠ a in l,(F.tuning a).Stable (F.epsilon a^2) 1) :
    Tendsto (fun a=>(F.layerPeriod B a:ℝ)*Real.sqrt (Real.sqrt (F.epsilon a))) l
      (𝓝 (Real.pi*Real.sqrt (2/(B*y/(2-y))))) ∧
      ∀ᶠ a in l,ResonanceWitness (F.tuning a) (F.epsilon a^2) 1 (F.layerPeriod B a) := by
  have hBp : 0<B := (Layer.Astar_pos F.theta_pos F.step_pos hy2).trans hBA
  let φ : ℝ := B*y/(2-y)
  have hφ : 0<φ := div_pos (mul_pos hBp F.step_pos) (by linarith)
  have hneg : Layer.polynomial θ y 0 B φ<0 := by
    rw [Layer.polynomial_minimum hy2]
    have hLambda := Layer.Lambda_neg_of_Astar_lt F.theta_pos F.step_pos hy2 hBA
    rw [Layer.Lambda,max_eq_left hBp.le] at hLambda
    have hh : θ*(2-y)<y*B^2 :=
      (lt_div_iff₀ (show 0<2-y by linarith)).mp (by linarith : θ<y*B^2/(2-y))
    exact mul_neg_of_pos_of_neg (div_pos (mul_pos (by norm_num) F.step_pos) (by linarith))
      (by nlinarith)
  have hx : Tendsto (fun a=>Layer.rationalXi φ (Real.sqrt (F.epsilon a))/
      Real.sqrt (F.epsilon a)) l (𝓝 φ) :=
    (Layer.rationalXi_scaled_tendsto hφ).comp F.sqrt_epsilon_tendstoGT
  have hp := F.layer_tail_tendsto (φ:=fun a=>Layer.rationalXi φ (Real.sqrt (F.epsilon a))/
    Real.sqrt (F.epsilon a)) 0 hB hx
  have hK := F.sqrt_epsilon_tendstoGT.eventually (Layer.rationalPeriod_eventually_ge_three hφ)
  constructor
  · exact (Layer.rationalPeriod_scaled_tendsto hφ).comp F.sqrt_epsilon_tendstoGT
  · filter_upwards [hp.eventually (eventually_lt_nhds hneg),hK,F.epsilon_pos,F.beta_eq,
      F.epsilon_zero.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),hstable]
      with a hn hK he hb he1 hs
    apply resonanceWitness_of_negative (F.tuning a) (sq_pos_of_pos he) (by nlinarith) hs hK
    have hmul : Real.sqrt (F.epsilon a)*(Layer.rationalXi φ (Real.sqrt (F.epsilon a))/
        Real.sqrt (F.epsilon a))=Layer.rationalXi φ (Real.sqrt (F.epsilon a)) := by
      field_simp [(Real.sqrt_pos.mpr he).ne']
    rw [hmul,scaledTail_zero] at hn
    have hneg' := (div_lt_iff₀ he).mp hn
    simp only [zero_mul] at hneg'
    simpa only [layerPeriod,φ,Layer.rationalXi,Layer.rationalAngle,mul_one,hb] using hneg'

end Scaling
end
end nesterov.TwoStep
