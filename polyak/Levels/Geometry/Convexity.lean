import polyak.Levels.Geometry.Arccotangent
import polyak.Levels.Geometry.DipSets

/-! Strict phase convexity below pi/2 and the one-dip theorem for every
shift and every signed lattice line. -/
noncomputable section
namespace polyak.Levels.Geometry
open General Set

def phaseBelow (q : Tuning) (s : ℝ) : Set ℝ :=
  {ω | ω∈Ioo 0 Real.pi ∧ shiftedAngle q s ω≤Real.pi/2}

theorem phaseBelow_convex (q : Tuning) (s : ℝ) : Convex ℝ (phaseBelow q s) := by
  have he : phaseBelow q s={ω∈Ioo 0 Real.pi | 0≤cotangent q ω+s} := by
    ext ω
    constructor
    · rintro ⟨hω,hθ⟩
      exact ⟨hω,(shiftedAngle_le_half_pi_iff q s hω).mp hθ⟩
    · rintro ⟨hω,hu⟩
      exact ⟨hω,(shiftedAngle_le_half_pi_iff q s hω).mpr hu⟩
  rw [he]
  exact ((cotangent_strictConcaveOn q).concaveOn.add_const s).convex_ge 0

theorem shiftedAngle_strictConvexOn (q : Tuning) (s : ℝ) :
    StrictConvexOn ℝ (phaseBelow q s) (shiftedAngle q s) := by
  apply strictConvexOn_of_deriv2_pos (phaseBelow_convex q s)
  · intro ω hω
    exact (hasDerivAt_shiftedAngle q s hω.1).continuousAt.continuousWithinAt
  · intro ω hω
    have hh:=interior_subset hω
    exact shiftedAngle_second_pos q s hh.1 hh.2

theorem phase_line_strictConvexOn (q : Tuning) (s n m : ℝ) :
    StrictConvexOn ℝ (phaseBelow q s) (fun ω=>shiftedAngle q s ω-(n*ω/2-Real.pi*m)) := by
  have hline : ConcaveOn ℝ (phaseBelow q s) (fun ω : ℝ=>n*ω/2-Real.pi*m) := by
    refine ⟨phaseBelow_convex q s,?_⟩
    intro x _ y _ a b _ _ hab
    simp only [smul_eq_mul]
    have he : n*(a*x+b*y)/2-Real.pi*m=
        a*(n*x/2-Real.pi*m)+b*(n*y/2-Real.pi*m) := by linear_combination (Real.pi*m)*hab
    exact he.ge
  exact (shiftedAngle_strictConvexOn q s).sub_concaveOn hline

/-- A lattice line of phase at most pi/2 cuts at most one dip, on any
interval of the curve's domain. No sign restriction is placed on its lag. -/
theorem one_dip_per_line (q : Tuning) (s n m : ℝ) {J : Set ℝ} (hJ : Convex ℝ J)
    (hdom : J⊆Icc 0 Real.pi) (hline : ∀ω∈J,n*ω/2-Real.pi*m≤Real.pi/2) :
    Convex ℝ {ω∈J | shiftedAngle q s ω<n*ω/2-Real.pi*m} := by
  have he : {ω∈J | shiftedAngle q s ω<n*ω/2-Real.pi*m}=
      J∩{ω∈phaseBelow q s | shiftedAngle q s ω-(n*ω/2-Real.pi*m)<0} := by
    ext ω
    constructor
    · rintro ⟨hj,hθ⟩
      have hd:=hdom hj
      have hph : shiftedAngle q s ω<Real.pi/2:=hθ.trans_le (hline ω hj)
      have h0 : 0<ω := by
        by_contra hn
        have he : ω=0:=le_antisymm (le_of_not_gt hn) hd.1
        rw [he,shiftedAngle_zero] at hph
        linarith [Real.pi_pos]
      have hp : ω<Real.pi := by
        by_contra hn
        have he : ω=Real.pi:=le_antisymm hd.2 (le_of_not_gt hn)
        rw [he,shiftedAngle_pi] at hph
        linarith [Real.pi_pos]
      exact ⟨hj,⟨⟨h0,hp⟩,hph.le⟩,by linarith⟩
    · rintro ⟨hj,_,hθ⟩
      exact ⟨hj,by linarith⟩
  rw [he]
  exact hJ.inter ((phase_line_strictConvexOn q s n m).convex_lt 0)

def closedDipReal (q : Tuning) (s : ℝ) : Set ℝ :=
  {ω | ω∈Icc 0 Real.pi ∧ shiftedAngle q s ω≤ω/2}

def dipReal (q : Tuning) (s : ℝ) : Set ℝ :=
  {ω | ω∈Icc 0 Real.pi ∧ shiftedAngle q s ω<ω/2}

theorem closedDipReal_convex (q : Tuning) (s : ℝ) : Convex ℝ (closedDipReal q s) := by
  have he : closedDipReal q s={ω∈phaseBelow q s | shiftedAngle q s ω-ω/2≤0} := by
    ext ω
    constructor
    · rintro ⟨hdom,hθ⟩
      have h0 : 0<ω := by
        by_contra hn
        have he : ω=0:=le_antisymm (le_of_not_gt hn) hdom.1
        rw [he,shiftedAngle_zero] at hθ
        linarith [Real.pi_pos]
      have hp : ω<Real.pi := by
        by_contra hn
        have he : ω=Real.pi:=le_antisymm hdom.2 (le_of_not_gt hn)
        rw [he,shiftedAngle_pi] at hθ
        linarith [Real.pi_pos]
      exact ⟨⟨⟨h0,hp⟩,by linarith⟩,by linarith⟩
    · rintro ⟨hdom,hθ⟩
      exact ⟨⟨hdom.1.1.le,hdom.1.2.le⟩,by linarith⟩
  rw [he]
  convert (phase_line_strictConvexOn q s 1 0).convexOn.convex_le 0 using 1
  ext ω
  simp only [one_mul,mul_zero,sub_zero]

theorem dipReal_convex (q : Tuning) (s : ℝ) : Convex ℝ (dipReal q s) := by
  convert one_dip_per_line q s 1 0 (convex_Icc 0 Real.pi) (Subset.refl _) (fun ω hω=>by
    simpa only [one_mul,mul_zero,sub_zero] using (div_le_div_of_nonneg_right hω.2 (by norm_num : (0:ℝ)≤2))) using 1
  ext ω
  simp only [dipReal,one_mul,mul_zero,sub_zero]

/-- Closed dips are genuine intervals in the original ordered frequency
space; the conclusion includes empty intervals and singleton tangencies. -/
theorem closedDip_ordConnected (q : Tuning) (s : ℝ) :
    (closedDip (shiftedCurve q s)).OrdConnected := by
  refine ⟨?_⟩
  intro a ha b hb c hc
  have ha' : (a:ℝ)∈closedDipReal q s:=⟨a.property,ha⟩
  have hb' : (b:ℝ)∈closedDipReal q s:=⟨b.property,hb⟩
  exact ((closedDipReal_convex q s).ordConnected.out ha' hb' hc).2

theorem dip_ordConnected (q : Tuning) (s : ℝ) :
    (dip (shiftedCurve q s)).OrdConnected := by
  refine ⟨?_⟩
  intro a ha b hb c hc
  have ha' : (a:ℝ)∈dipReal q s:=⟨a.property,ha⟩
  have hb' : (b:ℝ)∈dipReal q s:=⟨b.property,hb⟩
  exact ((dipReal_convex q s).ordConnected.out ha' hb' hc).2

end polyak.Levels.Geometry
