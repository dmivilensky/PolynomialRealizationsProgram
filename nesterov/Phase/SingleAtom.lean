import nesterov.Phase.Polar
import nesterov.Spectral.Finite
import nesterov.IQC.PolynomialSymbols

/-!
Article: Lemma `lem:single`, both signs of the phase and every integer lag.
Use: the exact rational-rotation criterion produces a genuine feasible measure.
-/
namespace nesterov.Phase
noncomputable section
open Spectral Set
open scoped NNReal Topology

def frequency (ω : ℝ) : Frequency := ⟨Real.cos ω,Real.neg_one_le_cos _,Real.cos_le_one _⟩

theorem arccos_frequency {ω : ℝ} (hω : ω∈Icc (0:ℝ) Real.pi) : Real.arccos (frequency ω)=ω :=
  Real.arccos_cos hω.1 hω.2

def singletonSpectrum (c : Frequency) : Spectrum :=
  finiteSpectrum (fun _ : Fin 1=>(1:ℝ≥0)) (fun _=>c) (by simp)

@[simp] theorem singleton_meanG (a : SymbolPair) (c : Frequency) :
    meanG (singletonSpectrum c) a=g a c := by
  simp [meanG,singletonSpectrum,polyak.Waves.finiteSpectrum_integral]

@[simp] theorem singleton_meanA (a : SymbolPair) (t : ℝ) (n : ℕ) (c : Frequency) :
    meanA (singletonSpectrum c) a t n=lagA a t n c := by
  simp [meanA,singletonSpectrum,polyak.Waves.finiteSpectrum_integral]

@[simp] theorem singleton_meanB (a : SymbolPair) (n : ℕ) (c : Frequency) :
    meanB (singletonSpectrum c) a n=lagB a n c := by
  simp [meanB,singletonSpectrum,polyak.Waves.finiteSpectrum_integral]

theorem singleton_feasible_iff (a : SymbolPair) (t C : ℝ) (c : Frequency) :
    Feasible a t (singletonSpectrum c) C ↔ |C|≤g a c ∧ ∀ n : ℕ,1≤n →
      0≤lagA a t n c-lagB a n c+C*Real.sinh (n*t) ∧
      0≤lagA a t n c+lagB a n c-C*Real.sinh (n*t) := by
  simp only [Feasible,singleton_meanG,singleton_meanA,singleton_meanB]

theorem phase_small_g_pos {g s : ℝ} {K : ℕ} (hK : 3≤K) (hne : g≠0 ∨ s≠0)
    (hphase : |angle g s|≤Real.pi/K) : 0<g := by
  have hk : (3:ℝ)≤K := by exact_mod_cast hK
  have hk0 : (0:ℝ)<K := by linarith
  have hp : Real.pi/(K:ℝ)<Real.pi/2 := (div_lt_div_iff_of_pos_left Real.pi_pos hk0 (by norm_num)).mpr (by linarith)
  have hΘ : angle g s∈Ioo (-(Real.pi/2)) (Real.pi/2) := by
    have hh := abs_le.mp hphase
    constructor <;> linarith
  have hh := mul_pos (magnitude_pos hne) (Real.cos_pos_of_mem_Ioo hΘ)
  rwa [magnitude_cos_angle] at hh

/-- The two source slacks are exactly the two nearest-vertex comparisons plus
one nonnegative hyperbolic term. -/
theorem singleton_slack_polar (a : SymbolPair) (t : ℝ) (c : Frequency) (n : ℕ) :
    lagA a t n c-lagB a n c=
      g a c*(Real.cosh (n*t)-1)+magnitude (g a c) (skew a c)*
        (Real.cos (angle (g a c) (skew a c))-
          Real.cos (n*Real.arccos c-angle (g a c) (skew a c))) ∧
    lagA a t n c+lagB a n c=
      g a c*(Real.cosh (n*t)-1)+magnitude (g a c) (skew a c)*
        (Real.cos (angle (g a c) (skew a c))-
          Real.cos (n*Real.arccos c+angle (g a c) (skew a c))) := by
  simp only [Real.cos_sub,Real.cos_add]
  have hg := magnitude_cos_angle (g a c) (skew a c)
  have hs := magnitude_sin_angle (g a c) (skew a c)
  dsimp [lagA,lagB]
  constructor <;> nlinarith [congrArg (fun x : ℝ=>x*Real.cos (n*Real.arccos c)) hg,
    congrArg (fun x : ℝ=>x*Real.sin (n*Real.arccos c)) hs]

/-- Every positive or negative exponent is admissible under the phase bound. -/
theorem singleton_feasible_of_phase {j K : ℕ} (hcop : j.Coprime K) (hK : 3≤K)
    (a : SymbolPair) (t : ℝ) (c : Frequency)
    (hω : Real.arccos c=2*Real.pi*j/K) (hne : g a c≠0 ∨ skew a c≠0)
    (hphase : |angle (g a c) (skew a c)|≤Real.pi/K) :
    0<g a c ∧ Feasible a t (singletonSpectrum c) 0 := by
  have hg := phase_small_g_pos hK hne hphase
  have hcos := (rational_phase_criterion hcop (by omega : 2≤K)
    (Complex.abs_arg_le_pi (mode (g a c) (skew a c)))).mpr hphase
  refine ⟨hg,(singleton_feasible_iff a t 0 c).mpr ⟨by simpa using hg.le,fun n hn=>?_⟩⟩
  have hh := singleton_slack_polar a t c n
  dsimp only [angle] at hh
  have hc := hcos n hn
  rw [←hω] at hc
  have hbase : 0≤g a c*(Real.cosh (n*t)-1) := mul_nonneg hg.le (by linarith [Real.one_le_cosh (n*t)])
  have hR : 0≤magnitude (g a c) (skew a c) := norm_nonneg _
  have hl := mul_le_mul_of_nonneg_left hc.1 hR
  have hu := mul_le_mul_of_nonneg_left hc.2 hR
  simp only [zero_mul,add_zero,sub_zero]
  constructor <;> nlinarith only [hh.1,hh.2,hbase,hl,hu]

/-- At t=0 feasibility forces exactly the source phase bound. -/
theorem singleton_feasible_zero_iff_phase {j K : ℕ} (hcop : j.Coprime K) (hK : 3≤K)
    (a : SymbolPair) (c : Frequency) (hω : Real.arccos c=2*Real.pi*j/K)
    (hne : g a c≠0 ∨ skew a c≠0) :
    Feasible a 0 (singletonSpectrum c) 0 ↔ |angle (g a c) (skew a c)|≤Real.pi/K := by
  constructor
  · intro h
    apply (rational_phase_criterion hcop (by omega : 2≤K)
      (Complex.abs_arg_le_pi (mode (g a c) (skew a c)))).mp
    intro n hn
    have hh := (singleton_feasible_iff a 0 0 c).mp h |>.2 n hn
    have hs := singleton_slack_polar a 0 c n
    dsimp only [angle] at hs
    simp only [mul_zero,Real.cosh_zero,sub_self,mul_zero,zero_add] at hs
    simp only [mul_zero,zero_mul,add_zero,sub_zero] at hh
    have hR := magnitude_pos hne
    rw [hω] at hs
    constructor <;> nlinarith [hs.1,hs.2]
  · exact fun h=>(singleton_feasible_of_phase hcop hK a 0 c hω hne h).2

end
end nesterov.Phase
