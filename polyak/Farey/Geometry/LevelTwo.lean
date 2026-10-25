import polyak.Farey.Geometry.Spines
import polyak.Levels.Geometry.Convexity
import polyak.Levels.Geometry.Gap

/-! The two actual line dips are intervals; level two is the literal
strict-between-consecutive-fan-points condition. -/
noncomputable section
namespace polyak.Farey
open General Levels Levels.Geometry Set

def gapWindow (K : ℕ) : Set ℝ := Ioo (2*Real.pi/((K:ℝ)+1)) (2*Real.pi/K)
def deltaU (q : Tuning) (K : ℕ) : Set ℝ :=
  {ω∈gapWindow K | q.angle ω<Real.pi-(K:ℝ)*ω/2}
def deltaV (q : Tuning) (K : ℕ) : Set ℝ :=
  {ω∈gapWindow K | q.angle ω<((K:ℝ)+1)*ω/2-Real.pi}

theorem gapWindow_domain {K : ℕ} (hK : 2≤K) : gapWindow K⊆Icc (0:ℝ) Real.pi := by
  intro ω hω
  have hk : (2:ℝ)≤K := by exact_mod_cast hK
  have hp : 0<(K:ℝ) := by linarith
  refine ⟨le_of_lt (lt_trans (by positivity) hω.1),?_⟩
  have he : 2*Real.pi/(K:ℝ)≤Real.pi := (div_le_iff₀ hp).mpr (by nlinarith [Real.pi_pos])
  exact hω.2.le.trans he

theorem shiftedAngle_no_shift (q : Tuning) (ω : ℝ) : shiftedAngle q 0 ω=q.angle ω := by
  simp only [shiftedAngle,shiftRadius,shiftNumerator,zero_mul,add_zero,Tuning.angle,Tuning.angleRadius]

theorem deltaU_convex (q : Tuning) {K : ℕ} (hK : 2≤K) : Convex ℝ (deltaU q K) := by
  have hk : (0:ℝ)<K := by positivity
  have hb : Real.pi/(K:ℝ)≤2*Real.pi/((K:ℝ)+1) := by
    rw [div_le_div_iff₀ hk (by positivity : (0:ℝ)<K+1)]
    have hh : (2:ℝ)≤K := by exact_mod_cast hK
    nlinarith [Real.pi_pos]
  have hline : ∀ω∈gapWindow K,-(K:ℝ)*ω/2-Real.pi*(-1)≤Real.pi/2 := by
    intro ω hω
    have hlo : Real.pi/(K:ℝ)≤ω := hb.trans hω.1.le
    have hh:=(div_le_iff₀ hk).mp hlo
    nlinarith
  have he:=one_dip_per_line q 0 (-(K:ℝ)) (-1) (convex_Ioo _ _) (gapWindow_domain hK) hline
  convert he using 1
  ext ω
  change (ω∈gapWindow K ∧ q.angle ω<Real.pi-(K:ℝ)*ω/2) ↔
    (ω∈gapWindow K ∧ shiftedAngle q 0 ω< -(K:ℝ)*ω/2-Real.pi*(-1))
  rw [shiftedAngle_no_shift,show -(K:ℝ)*ω/2-Real.pi*(-1)=Real.pi-(K:ℝ)*ω/2 by ring]

theorem deltaV_convex (q : Tuning) {K : ℕ} (hK : 2≤K) : Convex ℝ (deltaV q K) := by
  have hk : (0:ℝ)<K := by positivity
  have hline : ∀ω∈gapWindow K,((K:ℝ)+1)*ω/2-Real.pi*1≤Real.pi/2 := by
    intro ω hω
    have hu := (lt_div_iff₀ hk).mp hω.2
    have hd:=gapWindow_domain hK hω
    nlinarith [hd.2]
  have he:=one_dip_per_line q 0 ((K:ℝ)+1) 1 (convex_Ioo _ _) (gapWindow_domain hK) hline
  simpa only [deltaV,gapWindow,shiftedAngle_no_shift,mul_one] using he

theorem deltaU_ordConnected (q : Tuning) {K : ℕ} (hK : 2≤K) : (deltaU q K).OrdConnected :=
  (deltaU_convex q hK).ordConnected

theorem deltaV_ordConnected (q : Tuning) {K : ℕ} (hK : 2≤K) : (deltaV q K).OrdConnected :=
  (deltaV_convex q hK).ordConnected

def LevelTwoGap (K : ℕ) (q : Tuning) : Prop := Gap K q ∧
  ((deltaU q K).Nonempty ∧ ∃p : ℕ,1≤p ∧ closure (deltaU q K)⊆
    Ioo (2*Real.pi*p/fanDenominator K p) (2*Real.pi*(p+1)/fanDenominator K (p+1))) ∨
  (Gap K q ∧ (deltaV q K).Nonempty ∧ ∃m : ℕ,1≤m ∧ closure (deltaV q K)⊆
    Ioo (2*Real.pi*(upperSpine K (m+1)).1/(upperSpine K (m+1)).2)
      (2*Real.pi*(upperSpine K m).1/(upperSpine K m).2))

theorem phase_line_beyond {θ : ℝ} (hθ : 0<θ) (ω n m : ℝ) :
    θ≤n*ω/2-Real.pi*m ↔ 1≤n*Lattice.xi ω θ-m*Lattice.eta θ := by
  unfold Lattice.xi Lattice.eta
  have he : n*(ω/(2*θ))-m*(Real.pi/θ)=(n*ω/2-Real.pi*m)/θ := by field_simp
  rw [he,le_div_iff₀ hθ]
  simp only [one_mul]

end polyak.Farey
