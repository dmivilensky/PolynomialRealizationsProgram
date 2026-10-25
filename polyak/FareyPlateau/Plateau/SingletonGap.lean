import polyak.FareyPlateau.Plateau.SingletonPeriod
import polyak.Levels.Geometry.LevelZeroFull
import polyak.Levels.Geometry.LevelZeroExclusive
import polyak.Levels.Chart.TongueGraph

/-! A regular singleton at an interior Farey frequency must belong to its
original gap. This is a converse statement, with no gap premise. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels ModeLocking Set MeasureTheory

theorem singleton_regular_gap {q : Tuning} {L K : ℕ} {ω : Frequency}
    (D : RegularData q 0 L) (hS : Set.range D.atoms={ω})
    (hK : 2≤K) (hwin : Geometry.InWindow K ω)
    (hdip : ω∈Geometry.dip (tuningCurve q)) : Geometry.Gap K q := by
  change (tuningCurve q) ω<(ω:ℝ)/2 at hdip
  have hclosed : ω∈Geometry.closedDip (tuningCurve q) := by
    change (tuningCurve q) ω≤(ω:ℝ)/2
    exact hdip.le
  have hnf : ∀N:ℕ,∀hN:3≤N,Geometry.firstFrequency N (by omega)∉Geometry.closedDip (tuningCurve q) := by
    intro N hN hmem
    have hw := (Geometry.levelZero_grid_atom q hN hmem).2.1
    have hcar := D.program_carried (N':=nonzeroLags) (fun n hn=>D.lags_nonzero n hn) (by
      simpa only [Geometry.shiftedCurve_zero] using hw)
    rw [ae_dirac_eq] at hcar
    have he : Geometry.firstFrequency N (by omega)=ω := by
      rcases hcar with hz|⟨i,hi⟩
      · have hp : (0:ℝ)<(Geometry.firstFrequency N (by omega):ℝ) := by
          change 0<2*Real.pi/N
          positivity
        rw [hz] at hp
        exact (lt_irrefl _ hp).elim
      · have hω : D.atoms i=ω := by
          have hh : D.atoms i∈Set.range D.atoms := ⟨i,rfl⟩
          simpa only [hS,mem_singleton_iff] using hh
        exact hi.trans hω
    apply Geometry.firstFrequency_not_in_window hK hN
    rwa [he]
  rcases Geometry.levelZero_geometric_trichotomy q with hempty|hfirst|⟨_,J,⟨hJ,hW⟩,_⟩
  · rw [hempty] at hclosed
    exact (notMem_empty _ hclosed).elim
  · obtain ⟨N,hN,hmem⟩ := hfirst
    exact (hnf N hN hmem).elim
  · have he : J=K := Geometry.window_disjoint hJ hK (hW ω hclosed) hwin
    subst J
    exact Geometry.gap_of_closedDip_window q hK ⟨ω,hdip⟩ hW

theorem fraction_regular_singleton_gap {q : Tuning} {L K j k : ℕ}
    (D : RegularData q 0 L) (hK : 2≤K) (hf : Chart.FractionInWindow K j k)
    (b : ℤ) (hb : (b*(j:ℤ))%(k:ℤ)=1)
    (hS : Set.range D.atoms={Edge.atom j k hf.1 (Chart.fraction_window_arithmetic hK hf).2.le}) :
    Geometry.Gap K q := by
  obtain ⟨hj,hjk⟩ := Chart.fraction_window_arithmetic hK hf
  have hk : 3≤k := by omega
  let ω := Edge.atom j k hf.1 hjk.le
  have hphase : q.angle ω=Real.pi/k := by
    have hh := Edge.singleton_phase_eq D hk (by omega) hjk b hb hS
    simpa only [Geometry.shiftedCurve_zero,tuningCurve_apply] using hh
  apply singleton_regular_gap D hS hK
  · constructor
    · have hh := mul_lt_mul_of_pos_left hf.2.1 (by positivity : 0<2*Real.pi)
      change 2*Real.pi/((K:ℝ)+1)<2*Real.pi*j/k
      convert hh using 1 <;> ring
    · have hh := mul_lt_mul_of_pos_left hf.2.2 (by positivity : 0<2*Real.pi)
      change 2*Real.pi*j/k<2*Real.pi/(K:ℝ)
      convert hh using 1 <;> ring
  · change q.angle ω<(ω:ℝ)/2
    rw [hphase]
    change Real.pi/k<(2*Real.pi*j/k)/2
    have hpos : 0<Real.pi/(k:ℝ) := by positivity
    have hjR : (2:ℝ)≤j := by exact_mod_cast hj
    have he : (2*Real.pi*j/(k:ℝ))/2=(Real.pi/(k:ℝ))*j := by ring
    rw [he]
    nlinarith

end polyak.FareyPlateau
