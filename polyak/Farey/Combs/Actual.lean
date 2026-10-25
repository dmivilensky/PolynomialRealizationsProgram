import polyak.Farey.Combs.Positions
import polyak.Farey.Positions.Permutation
import polyak.Levels.Program.AtomicProgram

/-! The position program is exactly the original signed-lag program of
the actual two-atom measure. The minimizer constraint remains explicit. -/
noncomputable section
namespace polyak.Farey
open Levels MeasureTheory

def CombData.anchorFrequency (d : CombData) : Frequency :=
  gridFrequency d.k d.j d.k_pos (by have h:=d.j_ge;omega) d.j_half.le

def CombData.companionFrequency (d : CombData) : Frequency :=
  gridFrequency d.k d.i d.k_pos d.i_pos.le d.i_half.le

def CombData.anchorPhase (d : CombData) (Θ : Curve) : ℝ :=
  gridPhase Θ d.k d.j d.k_pos (by have h:=d.j_ge;omega) d.j_half.le

def CombData.companionPhase (d : CombData) (Θ : Curve) : ℝ :=
  gridPhase Θ d.k d.i d.k_pos d.i_pos.le d.i_half.le

structure Comb (Θ : Curve) where
  data : CombData
  coprime : Int.gcd data.j data.k=1
  anchor_phase : data.anchorPhase Θ=data.a
  companion_phase : data.companionPhase Θ=data.ac

theorem Comb.lag_columns {Θ : Curve} (C : Comb Θ) (n : ℤ) :
    Θ.lag n C.data.anchorFrequency=C.data.anchorColumn ((n*C.data.j)%C.data.k) ∧
    Θ.lag n C.data.companionFrequency=C.data.companionColumn ((n*C.data.j)%C.data.k) := by
  constructor
  · have h := lag_at_grid_eq_positionValue Θ C.data.k C.data.j n C.data.k_pos
      (by have h:=C.data.j_ge;omega) C.data.j_half.le
    change Θ.lag n C.data.anchorFrequency=positionValue C.data.k (C.data.anchorPhase Θ) _ at h
    rw [C.anchor_phase] at h
    exact h
  · have h := lag_at_grid_eq_positionValue Θ C.data.k C.data.i n C.data.k_pos C.data.i_pos.le C.data.i_half.le
    change Θ.lag n C.data.companionFrequency=positionValue C.data.k (C.data.companionPhase Θ) _ at h
    rw [C.companion_phase,residue_transport C.data.transport n] at h
    simpa only [CombData.companionColumn,residue,mul_comm] using h

theorem Comb.position_surjective {Θ : Curve} (C : Comb Θ) (p : ℤ)
    (hp : p∈C.data.positions) : ∃n : ℤ,(n*C.data.j)%C.data.k=p := by
  have he : C.data.j*Int.gcdA C.data.j C.data.k+C.data.k*Int.gcdB C.data.j C.data.k=1 := by
    simpa only [C.coprime,Nat.cast_one] using (Int.gcd_eq_gcd_ab C.data.j C.data.k).symm
  refine ⟨Int.gcdA C.data.j C.data.k*p,?_⟩
  obtain ⟨hp0,hpk⟩ := Finset.mem_Icc.mp hp
  have h := residue_eq_of_lattice (k:=C.data.k) (τ:=C.data.j)
    (p:=Int.gcdA C.data.j C.data.k*p) (y:=p) (q:= -Int.gcdB C.data.j C.data.k*p)
    (by omega) (by omega) (by linear_combination p*he)
  exact h

theorem Comb.all_lags_iff {Θ : Curve} (C : Comb Θ) (w0 wc : ℝ) :
    (∀n : ℤ,0≤w0*Θ.lag n C.data.anchorFrequency+wc*Θ.lag n C.data.companionFrequency) ↔
    ∀p∈C.data.positions,0≤w0*C.data.anchorColumn p+wc*C.data.companionColumn p := by
  constructor
  · intro h p hp
    obtain ⟨n,hn⟩ := C.position_surjective p hp
    have hh := h n
    rw [(C.lag_columns n).1,(C.lag_columns n).2,hn] at hh
    exact hh
  · intro h n
    rw [(C.lag_columns n).1,(C.lag_columns n).2]
    let p := (n*C.data.j)%C.data.k
    have hp0 : 0≤p := Int.emod_nonneg _ C.data.k_pos.ne'
    have hpk : p < C.data.k := Int.emod_lt_of_pos _ C.data.k_pos
    by_cases hp : p=0
    · change 0≤w0*C.data.anchorColumn p+wc*C.data.companionColumn p
      simp only [hp,CombData.anchorColumn,CombData.companionColumn,residue,
        zero_mul,Int.zero_emod,Int.cast_zero,positionValue_zero,mul_zero,add_zero,le_refl]
    · exact h p (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)

def Comb.measure {Θ : Curve} (C : Comb Θ) (w0 wc : NNReal) : Measure Frequency :=
  atomicMeasure (fun b : Bool=>if b then wc else w0)
    (fun b : Bool=>if b then C.data.companionFrequency else C.data.anchorFrequency)

instance Comb.finite_measure {Θ : Curve} (C : Comb Θ) (w0 wc : NNReal) :
    IsFiniteMeasure (C.measure w0 wc) := inferInstanceAs (IsFiniteMeasure (atomicMeasure _ _))

theorem Comb.integral_measure {Θ : Curve} (C : Comb Θ) (w0 wc : NNReal) (f : Frequency→ℝ) :
    (∫ω,f ω∂C.measure w0 wc)=(w0:ℝ)*f C.data.anchorFrequency+(wc:ℝ)*f C.data.companionFrequency := by
  rw [measure,atomicMeasure_integral]
  rw [Fintype.sum_bool]
  exact add_comm _ _

theorem Comb.program_iff {Θ : Curve} (C : Comb Θ) (w0 wc : NNReal)
    (hw0 : 0 < w0) (hwc : 0 < wc) :
    ProgramSolution Θ nonzeroLags (C.measure w0 wc) ↔
      (0≤(w0:ℝ)*Θ.minimizer C.data.anchorFrequency+(wc:ℝ)*Θ.minimizer C.data.companionFrequency) ∧
      (∀p∈C.data.positions,0≤(w0:ℝ)*C.data.anchorColumn p+(wc:ℝ)*C.data.companionColumn p) := by
  have hne : C.measure w0 wc≠0 := by
    apply atomicMeasure_ne_zero
    rw [Fintype.sum_bool]
    exact add_pos hwc hw0
  constructor
  · intro h
    refine ⟨by simpa only [C.integral_measure] using h.2.2.1,?_⟩
    apply (C.all_lags_iff _ _).mp
    intro n
    by_cases hn : n=0
    · subst n
      simp only [Curve.lag_zero,mul_zero,add_zero,le_refl]
    · have hh := h.2.2.2 n hn
      simpa only [C.integral_measure] using hh
  · rintro ⟨hm,hl⟩
    refine ⟨inferInstance,hne,by simpa only [C.integral_measure] using hm,?_⟩
    intro n _
    rw [C.integral_measure]
    exact (C.all_lags_iff _ _).mpr hl n

end polyak.Farey
