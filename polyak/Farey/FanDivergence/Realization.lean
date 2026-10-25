import polyak.Farey.FanDivergence.Program
import polyak.Farey.FanDivergence.Orbit

/-! The finite fan LP is the actual two-atom full measure program.
Its feasible solutions yield genuine periodic heavy-ball trajectories. -/
noncomputable section
namespace polyak.Farey
open polyak.General polyak.Levels MeasureTheory

theorem gridFrequency_mem_grid (k i : ℤ) (hk : 0<k) (hi : 0< i) (hik : 2*i≤k) :
    gridFrequency k i hk hi.le hik∈periodicGrid k.toNat := by
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hiR : (0:ℝ)< i := by exact_mod_cast hi
  have hcast : (k.toNat:ℝ)=(k:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk.le
  refine ⟨by change 0<2*Real.pi*i/k;positivity,i,?_⟩
  change (k.toNat:ℝ)*(2*Real.pi*i/k)=(i:ℝ)*(2*Real.pi)
  rw [hcast]
  field_simp

def fanPairFrequencies (P : FanParameters) : Fin 2→Frequency := ![P.companion,P.anchor]

def FanAtomicProgram (P : FanParameters) (Θ : Curve) : Prop :=
  ∃u v : NNReal,0<u+v ∧
    ProgramSolution Θ nonzeroLags (atomicMeasure ![u,v] (fanPairFrequencies P))

theorem fanPairFrequencies_mem_grid (P : FanParameters) (j : Fin 2) :
    fanPairFrequencies P j∈periodicGrid P.k.toNat := by
  fin_cases j
  · exact gridFrequency_mem_grid P.k (P.p-1) P.k_pos P.companion_pos P.companion_le
  · exact gridFrequency_mem_grid P.k P.p P.k_pos P.p_pos P.two_p_lt_k.le

theorem fan_finiteProgram_iff_atomic (P : FanParameters) (Θ : Curve) :
    FanFiniteProgram P Θ ↔ FanAtomicProgram P Θ := by
  have hk : 0<P.k.toNat := by have := P.k_pos;omega
  have hcast : (P.k.toNat:ℤ)=P.k := Int.toNat_of_nonneg P.k_pos.le
  constructor
  · rintro ⟨u,v,hu,hv,hne,hmin,hlag⟩
    let u' : NNReal := ⟨u,hu⟩
    let v' : NNReal := ⟨v,hv⟩
    have hne' : 0<u'+v' := hne
    refine ⟨u',v',hne',?_⟩
    have hw : 0<∑j : Fin 2,(![u',v'] j : NNReal) := by simpa [Fin.sum_univ_two] using hne'
    apply (atomic_program_iff Θ hk ![u',v'] (fanPairFrequencies P) hw (fanPairFrequencies_mem_grid P)).mpr
    constructor
    · rw [Fin.sum_univ_two]
      change 0≤u*Θ.minimizer P.companion+v*Θ.minimizer P.anchor
      exact hmin
    · intro n hn hnk
      have hnZ : (0:ℤ)<n := by exact_mod_cast hn
      have hnkZ : (n:ℤ)<P.k := by
        have hh : (n:ℤ)<(P.k.toNat:ℤ) := by exact_mod_cast hnk
        rwa [hcast] at hh
      rw [Fin.sum_univ_two]
      change 0≤fanLagSum P Θ u v n
      exact hlag n hnZ hnkZ
  · rintro ⟨u,v,hne,hs⟩
    have hw : 0<∑j : Fin 2,(![u,v] j : NNReal) := by simpa [Fin.sum_univ_two] using hne
    obtain ⟨hmin,hlag⟩ := (atomic_program_iff Θ hk ![u,v] (fanPairFrequencies P) hw
      (fanPairFrequencies_mem_grid P)).mp hs
    refine ⟨u,v,u.property,v.property,?_,?_,?_⟩
    · exact_mod_cast hne
    · simpa only [Fin.sum_univ_two,fanPairFrequencies,Matrix.cons_val_zero,Matrix.cons_val_one] using hmin
    · intro n hn hnk
      have hnNat : 0<n.toNat := by omega
      have hnkNat : n.toNat<P.k.toNat := (Int.toNat_lt_toNat P.k_pos).mpr hnk
      have hh := hlag n.toNat hnNat hnkNat
      simpa only [Fin.sum_univ_two,fanPairFrequencies,Matrix.cons_val_zero,Matrix.cons_val_one,
        fanLagSum,Int.toNat_of_nonneg hn.le] using hh

theorem fan_atomic_periodicFP (P : FanParameters) (Θ : Curve) (h : FanAtomicProgram P Θ) :
    PeriodicFP Θ P.k.toNat := by
  obtain ⟨u,v,_hne,hs⟩ := h
  exact ⟨_,hs,atomicMeasure_carried_grid ![u,v] (fanPairFrequencies P) P.k.toNat
    (fanPairFrequencies_mem_grid P)⟩

theorem fan_actual_two_harmonic_orbit (P : FanParameters) (q : Tuning)
    (h : FanFiniteProgram P (tuningCurve q)) : FanPeriodicOrbit q P.k.toNat 2 ∧ 1≤q.rate := by
  obtain ⟨u,v,hne,hs⟩ := (fan_finiteProgram_iff_atomic P (tuningCurve q)).mp h
  have hw : 0<∑j : Fin 2,(![u,v] j : NNReal) := by simpa [Fin.sum_univ_two] using hne
  have horbit : FanPeriodicOrbit q P.k.toNat (Fintype.card (Fin 2)) :=
    atomic_periodic_actual_orbit q (J:=Fin 2) ![u,v] (fanPairFrequencies P) hw
    (fanPairFrequencies_mem_grid P) hs
  rw [Fintype.card_fin] at horbit
  exact ⟨horbit,fp_one_le_rate q ⟨_,hs⟩⟩

theorem fan_divergence_admissible_ratio (P : FanParameters) (q : Tuning)
    (hmain : P.firstAngle<(tuningCurve q) P.anchor ∧ (tuningCurve q) P.anchor≤P.halfAnchor)
    (hcomp : P.halfCompanion<(tuningCurve q) P.companion ∧
      (tuningCurve q) P.companion<P.companionAngle)
    (hcompHalf : (tuningCurve q) P.companion≤Real.pi/2)
    (hr : ∃r : ℝ,FanRatioAdmissible P (tuningCurve q) r ∧
      ∀n : ℤ,2≤n→n<P.k→n≠P.parentResidue→0≤fanLagSum P (tuningCurve q) r 1 n) :
    FanPeriodicOrbit q P.k.toNat 2 ∧ 1≤q.rate := by
  obtain ⟨r,hr,hremaining⟩ := hr
  exact fan_actual_two_harmonic_orbit P q
    (fan_finiteProgram_of_ratio P (tuningCurve q) hmain hcomp hcompHalf hr hremaining)

theorem p2_atomicProgram_iff_displayed (P : FanParameters) (hp : P.p=2) (Θ : Curve)
    (hcomp : P.firstAngle<Θ P.companion ∧ Θ P.companion≤P.halfAnchor)
    (hmain : P.firstAngle<Θ P.anchor ∧ Θ P.anchor≤P.halfAnchor) :
    FanAtomicProgram P Θ ↔ 0≤fanP2Expression P Θ :=
  (fan_finiteProgram_iff_atomic P Θ).symm.trans (p2_finiteProgram_iff_displayed P hp Θ hcomp hmain)

theorem p2_actual_divergence (P : FanParameters) (hp : P.p=2) (q : Tuning)
    (hcomp : P.firstAngle<(tuningCurve q) P.companion ∧ (tuningCurve q) P.companion≤P.halfAnchor)
    (hmain : P.firstAngle<(tuningCurve q) P.anchor ∧ (tuningCurve q) P.anchor≤P.halfAnchor)
    (hdisplayed : 0≤fanP2Expression P (tuningCurve q)) :
    FanPeriodicOrbit q P.k.toNat 2 ∧ 1≤q.rate :=
  fan_actual_two_harmonic_orbit P q
    ((p2_finiteProgram_iff_displayed P hp (tuningCurve q) hcomp hmain).mpr hdisplayed)

end polyak.Farey
