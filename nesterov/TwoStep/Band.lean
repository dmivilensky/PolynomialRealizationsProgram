import nesterov.TwoStep.Phase
import Mathlib.Algebra.Order.Floor.Ring

/-! Lemma band: an integer resonant period in a frequency band. -/
namespace nesterov.TwoStep
noncomputable section
open Set Filter
open scoped Topology

theorem exists_integer_period_band {s a b : ℝ} (hs : s∈Ico (0:ℝ) 1)
    (ha : 0<a) (hab : a<b) (hb : b≤2*Real.pi/3)
    (hwidth : 1≤2*Real.pi*(1-s)/a-2*Real.pi*(1+s)/b) :
    ∃ K : ℕ,3≤K ∧ 2*Real.pi*(1+s)/b≤K ∧
      Icc ((1-s)*(2*Real.pi/K)) ((1+s)*(2*Real.pi/K))⊆Icc a b := by
  let u : ℝ := 2*Real.pi*(1+s)/b
  let K : ℕ := Nat.ceil u
  have hbpos : 0<b := ha.trans hab
  have hu : 0<u := div_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) (by linarith [hs.1])) hbpos
  have hle : u≤(K:ℝ) := Nat.le_ceil u
  have hlt : (K:ℝ)<u+1 := Nat.ceil_lt_add_one hu.le
  have hKreal : 3≤(K:ℝ) := by
    have hh : 3≤u := (le_div_iff₀ hbpos).mpr (by nlinarith [hs.1,Real.pi_pos])
    exact hh.trans hle
  have hK : 3≤K := by exact_mod_cast hKreal
  have hKpos : (0:ℝ)<K := by linarith
  have hupper : (K:ℝ)≤2*Real.pi*(1-s)/a := by dsimp [u] at hlt;linarith
  refine ⟨K,hK,hle,?_⟩
  intro ω hω
  constructor
  · have hh : a≤(1-s)*(2*Real.pi/K) := by
      rw [←mul_div_assoc]
      apply (le_div_iff₀ hKpos).mpr
      have h := (le_div_iff₀ ha).mp hupper
      simpa only [mul_comm,mul_left_comm,mul_assoc] using h
    exact hh.trans hω.1
  · have hh : (1+s)*(2*Real.pi/K)≤b := by
      rw [←mul_div_assoc]
      apply (div_le_iff₀ hKpos).mpr
      have h := (div_le_iff₀ hbpos).mp hle
      simpa only [u,mul_comm,mul_left_comm,mul_assoc] using h
    exact hω.2.trans hh

theorem negative_band_restRate (q : Momentum.Tuning) {μ L a b : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L)
    (ha : 0<a) (hab : a<b) (hb : b≤2*Real.pi/3)
    (hwidth : 1≤2*Real.pi/a-2*Real.pi/b)
    (hneg : ∀ ω∈Icc a b,Ltau q.beta q.tau (q.stepSize*μ) (q.stepSize*L) (1-Real.cos ω)<0) :
    ∃ K : ℕ,3≤K ∧ 2*Real.pi/b≤K ∧
      1<Momentum.momentumRestRate q.beta q.tau q.stepSize q.step_pos.ne' μ L := by
  obtain ⟨K,hK,hlo,hband⟩ := exists_integer_period_band (s:=0) (by norm_num) ha hab hb (by simpa using hwidth)
  have hmem : 2*Real.pi/K∈Icc a b := by
    apply hband
    simp only [sub_zero,add_zero,one_mul,mem_Icc,le_refl,and_self]
  exact ⟨K,hK,by simpa using hlo,negative_Ltau_restRate q hμ hμL hs hK (hneg _ hmem)⟩

/-- A fixed from-rest objective in real dimension three approaching a periodic orbit. -/
def HasPeriodicRestWitness (q : Momentum.Tuning) (μ L : ℝ) (K : ℕ) : Prop :=
  ∃ f : EuclideanSpace ℝ (Fin 3)→ℝ,polyak.CenteredSmoothStronglyConvex μ L f ∧
    ∃ x₀ : EuclideanSpace ℝ (Fin 3),x₀≠0 ∧
      ∃ orbit : ℕ→EuclideanSpace ℝ (Fin 3),Function.Periodic orbit K ∧
        Tendsto (fun n=>Momentum.iterate (gradient f) q.beta q.tau q.stepSize x₀ n-orbit n)
          Filter.atTop (𝓝 0) ∧ ∃ c₀ : ℝ,0<c₀ ∧ ∀ n : ℕ,
            c₀*‖x₀‖≤‖Momentum.iterate (gradient f) q.beta q.tau q.stepSize x₀ n‖

theorem negative_Ltau_periodic_rest (q : Momentum.Tuning) {μ L : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hs : q.Stable μ L) {K : ℕ} (hK : 3≤K)
    (hneg : Ltau q.beta q.tau (q.stepSize*μ) (q.stepSize*L)
      (1-Real.cos (2*Real.pi/K))<0) :
    HasPeriodicRestWitness q μ L K := by
  have hangle : 2*Real.pi/K∈Ioo (0:ℝ) Real.pi := by
    simpa [polyak.General.Regions.rationalAngle] using
      polyak.General.Regions.rationalAngle_mem (j:=1) (k:=K) le_rfl (by omega)
  have hp := (stable_Ltau_phase_sign q hμ hμL hs ⟨hangle.1,hangle.2.le⟩).2.2.mp hneg
  have hphase : Phase.momentumAngle q μ L (2*Real.pi*1/K)≤Real.pi/K := by
    rw [mul_one]
    rw [show 2*Real.pi/(K:ℝ)/2=Real.pi/K by ring] at hp
    exact hp.le
  obtain ⟨f,hf,x₀,hx₀,c₀,hc₀,P,hlower,hperiod,happroach⟩ :=
    Phase.exists_periodic_startup q hμ hμL hs hK (j:=1) le_rfl (by omega) (by simp)
      (by simpa only [Nat.cast_one] using hphase)
  exact ⟨f,hf,x₀,hx₀,_,hperiod,happroach,c₀,hc₀,hlower⟩

end
end nesterov.TwoStep
