import polyak.General.Regions.SingleHarmonic
import polyak.General.Regions.OneAtom
import polyak.General.AngleSource

/-! Article: Proposition single, in the original spectral-feasibility model. -/
namespace polyak.General.Regions
noncomputable section
open Spectral

/-- A primitive root-of-unity frequency in the paper's angle coordinate. -/
def rationalAngle (j k : ℕ) : ℝ := 2*Real.pi*j/k

/-- The cosine coordinate used by the existing full interpolation machinery. -/
def cosineFrequency (ω : ℝ) : Frequency :=
  ⟨Real.cos ω,Real.neg_one_le_cos _,Real.cos_le_one _⟩

theorem rationalAngle_mem {j k : ℕ} (hj : 1≤j) (hjk : 2*j<k) :
    rationalAngle j k∈Set.Ioo 0 Real.pi := by
  have hk : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hj0 : (0:ℝ)<j := by exact_mod_cast (show 0<j by omega)
  dsimp [rationalAngle]
  constructor
  · positivity
  · apply (div_lt_iff₀ hk).mpr
    have hcast : (2:ℝ)*j<k := by exact_mod_cast hjk
    nlinarith [Real.pi_pos]

/-- At t=0, the two raw source slacks are the two cosine differences. -/
theorem oneAtom_zero_feasible_iff_phase (q : Tuning) {ω : ℝ}
    (hω : ω∈Set.Ioo 0 Real.pi) :
    Waves.MixtureFeasible (oneAtom (cosineFrequency ω))
      (Waves.multiplierMap q.A q.B q.beta 0) 0 0 ↔
    0≤Real.cos (q.angle ω) ∧ ∀ n : ℕ,1≤n →
      Real.cos (n*ω-q.angle ω)≤Real.cos (q.angle ω) ∧
      Real.cos (n*ω+q.angle ω)≤Real.cos (q.angle ω) := by
  have har : Real.arccos ((cosineFrequency ω):ℝ)=ω :=
    Real.arccos_cos hω.1.le hω.2.le
  have hm : Waves.multiplierMap q.A q.B q.beta 0 (cosineFrequency ω)=q.m (Waves.z 0 ω) := by
    change Waves.multiplier q.A q.B q.beta 0 (Real.arccos ((cosineFrequency ω):ℝ))=q.m _
    rw [har]
    rfl
  have hR : 0<q.polarRadius ω := q.polarRadius_pos ⟨hω.1.le,hω.2.le⟩
  rw [oneAtom_feasible_iff,har,hm,q.g_polar ⟨hω.1.le,hω.2.le⟩]
  simp only [abs_zero,mul_zero,Real.cosh_zero,Real.sinh_zero,sub_zero,add_zero]
  have hl (n : ℕ) : q.polarRadius ω*Real.cos (q.angle ω)*(1-Real.cos (n*ω))-
      2*(q.m (Waves.z 0 ω)).im*Real.sin (n*ω)=
      q.polarRadius ω*(Real.cos (q.angle ω)-Real.cos (n*ω-q.angle ω)) := by
    rw [q.im_polar ⟨hω.1.le,hω.2.le⟩,Real.cos_sub]
    ring
  have hu (n : ℕ) : q.polarRadius ω*Real.cos (q.angle ω)*(1-Real.cos (n*ω))+
      2*(q.m (Waves.z 0 ω)).im*Real.sin (n*ω)=
      q.polarRadius ω*(Real.cos (q.angle ω)-Real.cos (n*ω+q.angle ω)) := by
    rw [q.im_polar ⟨hω.1.le,hω.2.le⟩,Real.cos_add]
    ring
  simp only [hl,hu,mul_nonneg_iff_of_pos_left hR,sub_nonneg]

/-- Proposition single, full iff with all lags and the minimizer constraint. -/
theorem single_harmonic_feasible_iff (q : Tuning) {j k : ℕ}
    (hcop : j.Coprime k) (hj : 1≤j) (hjk : 2*j<k) :
    Waves.MixtureFeasible (oneAtom (cosineFrequency (rationalAngle j k)))
      (Waves.multiplierMap q.A q.B q.beta 0) 0 0 ↔
      q.angle (rationalAngle j k)≤Real.pi/k := by
  have hω := rationalAngle_mem hj hjk
  have hθ := q.angle_mem hω
  have hk : 2≤k := by omega
  rw [oneAtom_zero_feasible_iff_phase q hω]
  have hp := single_harmonic_phase_criterion (j:=j) hcop hk hθ.1.le hθ.2.le
  change _∧(∀ n : ℕ,1≤n → Real.cos (n*(2*Real.pi*j/k)-q.angle (rationalAngle j k))≤_ ∧
      Real.cos (n*(2*Real.pi*j/k)+q.angle (rationalAngle j k))≤_) ↔ _
  rw [hp]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_,h⟩
    have hhalf : Real.pi/k≤Real.pi/2 := by
      apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
      exact_mod_cast hk
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos,hθ.1],h.trans hhalf⟩

/-- A feasible rational frequency gives the actual nonconvergence rate lower bound. -/
theorem one_le_rate_of_rational_phase (q : Tuning) {j k : ℕ}
    (hcop : j.Coprime k) (hj : 1≤j) (hjk : 2*j<k)
    (hphase : q.angle (rationalAngle j k)≤Real.pi/k) :
    1≤Dynamics.rate q.x q.y 1 q.beta := by
  have h := oneAtom_exp_le_originalRate q (cosineFrequency (rationalAngle j k))
    ((single_harmonic_feasible_iff q hcop hj hjk).mpr hphase)
    (fun ht=>False.elim (lt_irrefl (0:ℝ) ht))
  simpa only [Real.exp_zero] using h

end
end polyak.General.Regions
