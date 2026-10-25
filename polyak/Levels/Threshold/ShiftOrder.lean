import polyak.Levels.Program.Monotonicity
import polyak.Levels.Lattice.Atoms
import polyak.Levels.Geometry.Arccotangent
import polyak.Levels.Geometry.CotangentBound
import polyak.Levels.Program.Grid

/-! Order, finite witnesses and finite lower bounds for the shifted programs. -/
noncomputable section
open MeasureTheory
namespace polyak.Levels.Threshold

theorem shiftedCurve_le_of_cotangent_le {q q' : General.Tuning} {s s' : ℝ}
    (h : ∀ω∈Set.Ioo 0 Real.pi,Geometry.cotangent q ω+s≤Geometry.cotangent q' ω+s') :
    ∀ω:Frequency,Geometry.shiftedCurve q' s' ω≤Geometry.shiftedCurve q s ω := by
  intro ω
  rcases eq_or_lt_of_le ω.property.1 with h0|h0
  · have he : ω=frequencyZero := Subtype.ext h0.symm
    rw [he,(Geometry.shiftedCurve q s).at_zero,(Geometry.shiftedCurve q' s').at_zero]
  rcases eq_or_lt_of_le ω.property.2 with hp|hp
  · have he : ω=frequencyPi := Subtype.ext hp
    rw [he,(Geometry.shiftedCurve q s).at_pi,(Geometry.shiftedCurve q' s').at_pi]
  change Geometry.shiftedAngle q' s' ω≤Geometry.shiftedAngle q s ω
  rw [Geometry.shiftedAngle_eq_arccotangent q s ⟨h0,hp⟩,
    Geometry.shiftedAngle_eq_arccotangent q' s' ⟨h0,hp⟩]
  unfold Geometry.arccotangent
  have ha := Real.arctan_le_arctan_iff.mpr (h ω ⟨h0,hp⟩)
  linarith

theorem shifted_fpOn_mono (q : General.Tuning) (𝒩 : Set ℤ) {s t : ℝ} (hst : s≤t)
    (hs : FPOn (Geometry.shiftedCurve q s) 𝒩) : FPOn (Geometry.shiftedCurve q t) 𝒩 :=
  fpOn_mono 𝒩 (shiftedCurve_le_of_cotangent_le (fun _ _ => by linarith)) hs

def periodicFrequency (k : ℕ) (hk : 2≤k) : Frequency :=
  ⟨2*Real.pi/k,by
    have hkR : (2:ℝ)≤k := by exact_mod_cast hk
    constructor
    · positivity
    · apply (div_le_iff₀ (show (0:ℝ)<k by linarith)).mpr
      nlinarith [Real.pi_pos]⟩

def atomicShift (q : General.Tuning) (k : ℕ) : ℝ :=
  Real.cos (Real.pi/k)/Real.sin (Real.pi/k)-Geometry.cotangent q (2*Real.pi/k)

theorem atomicShift_phase (q : General.Tuning) {k : ℕ} (hk : 3≤k) :
    Geometry.shiftedCurve q (atomicShift q k) (periodicFrequency k (by omega))=Real.pi/k := by
  have hkR : (3:ℝ)≤k := by exact_mod_cast hk
  have hw : 2*Real.pi/k∈Set.Ioo 0 Real.pi := by
    constructor
    · positivity
    · apply (div_lt_iff₀ (show (0:ℝ)<k by linarith)).mpr
      nlinarith [Real.pi_pos]
  have hphase : Real.pi/k∈Set.Ioo 0 Real.pi := by
    constructor
    · positivity
    · apply (div_lt_iff₀ (show (0:ℝ)<k by linarith)).mpr
      nlinarith [Real.pi_pos]
  apply Geometry.angle_eq_of_cot_eq (Geometry.shiftedAngle_mem q _ hw) hphase
  rw [Geometry.cot_shiftedAngle q _ hw]
  dsimp [atomicShift,Geometry.cotangent]
  ring

theorem atomicShift_solution (q : General.Tuning) {k : ℕ} (hk : 3≤k) :
    ProgramSolution (Geometry.shiftedCurve q (atomicShift q k)) nonzeroLags
      (Measure.dirac (periodicFrequency k (by omega))) := by
  apply (Lattice.rational_atom_program_iff _ (Nat.coprime_one_left k) (by omega)
    (periodicFrequency k (by omega)) (by simp [periodicFrequency])).mpr
  exact (atomicShift_phase q hk).le

theorem shifted_fpOn_nonempty (q : General.Tuning) (𝒩 : Set ℤ) (hN : 𝒩⊆nonzeroLags) :
    ∃s:ℝ,FPOn (Geometry.shiftedCurve q s) 𝒩 := by
  exact ⟨atomicShift q 3,_,(atomicShift_solution q (by norm_num : 3≤3)).relax hN⟩

theorem periodicFrequency_mem_grid {k : ℕ} (hk : 2≤k) : periodicFrequency k hk∈periodicGrid k := by
  refine ⟨?_,1,?_⟩
  · change 0<2*Real.pi/(k:ℝ)
    have hkR : (0:ℝ)<k := by exact_mod_cast (by omega : 0<k)
    positivity
  · simp only [Int.cast_one]
    change (k:ℝ)*(2*Real.pi/(k:ℝ))=(1:ℝ)*(2*Real.pi)
    have hkR : (k:ℝ)≠0 := by exact_mod_cast (by omega : k≠0)
    field_simp

theorem shifted_periodic_nonempty (q : General.Tuning) {k : ℕ} (hk : 3≤k) :
    ∃s:ℝ,PeriodicFP (Geometry.shiftedCurve q s) k := by
  refine ⟨atomicShift q k,Measure.dirac (periodicFrequency k (by omega)),atomicShift_solution q hk,?_⟩
  simpa only [ae_dirac_eq,Filter.eventually_pure] using periodicFrequency_mem_grid (by omega)

theorem fpOn_impossible_of_negative_minimizer (Θ : Curve) (𝒩 : Set ℤ)
    (hneg : ∀ω,Θ.minimizer ω<0) : ¬FPOn Θ 𝒩 := by
  let S : CertificateSymbol Θ 𝒩 := {
    lags:=∅,lags_subset:=by simp,weight:=fun _=>0,weight_nonneg:=by simp,gamma:=1,gamma_nonneg:=by norm_num }
  obtain ⟨T⟩ := strictSymbol_of_pointwise_negative S (by
    intro ω
    simpa only [S,CertificateSymbol.eval,Finset.sum_empty,zero_add,one_mul] using hneg ω)
  exact T.not_fpOn

theorem shifted_fpOn_lower_bound (q : General.Tuning) (𝒩 : Set ℤ) {s : ℝ}
    (hs : FPOn (Geometry.shiftedCurve q s) 𝒩) : -Geometry.cotangentUpper q≤s := by
  by_contra hn
  have hslow : s< -Geometry.cotangentUpper q := lt_of_not_ge hn
  apply (fpOn_impossible_of_negative_minimizer (Geometry.shiftedCurve q s) 𝒩 ?_) hs
  intro ω
  rcases eq_or_lt_of_le ω.property.1 with h0|h0
  · have he : ω=frequencyZero := Subtype.ext h0.symm
    rw [he,(Geometry.shiftedCurve q s).minimizer_at_zero]
    norm_num
  rcases eq_or_lt_of_le ω.property.2 with hp|hp
  · have he : ω=frequencyPi := Subtype.ext hp
    rw [he,(Geometry.shiftedCurve q s).minimizer_at_pi]
    norm_num
  have hprof : Geometry.cotangent q ω+s<0 := by
    linarith [Geometry.cotangent_le_upper q ⟨h0,hp⟩]
  have he := Geometry.cot_shiftedAngle q s ⟨h0,hp⟩
  have hmem := Geometry.shiftedAngle_mem q s ⟨h0,hp⟩
  have hsin := Real.sin_pos_of_pos_of_lt_pi hmem.1 hmem.2
  have he' := (div_eq_iff hsin.ne').mp he
  change Real.cos (Geometry.shiftedAngle q s ω)<0
  rw [he']
  exact mul_neg_of_neg_of_pos hprof hsin

end polyak.Levels.Threshold
