import polyak.General.RootsDominant

/-! Source §6.1: the two damping curves bound the regime for EVERY
curvature in the closed interval, with both critically damped ends retained. -/
noncomputable section
namespace polyak.General.Tuning

theorem all_curvatures_damping_iff (q : Tuning) :
    (∀ lam : ℝ,lam∈Set.Icc q.x q.y → (1+q.beta-lam)^2≤4*q.beta) ↔
      q.rhoQ=Real.sqrt q.beta := by
  constructor
  · intro h
    have ha:=rootRadius_eq_sqrt (h q.x ⟨le_rfl,q.x_lt_y.le⟩)
    have hb:=rootRadius_eq_sqrt (h q.y ⟨q.x_lt_y.le,le_rfl⟩)
    simp only [rhoQ,rhoA,rhoB,ha,hb,max_self]
  · intro h lam hlam
    have hd:=q.damping_iff.mp h
    have hs:=Real.sq_sqrt q.beta_nonneg
    have hs0:=Real.sqrt_nonneg q.beta
    have hu : 1+q.beta-lam≤2*Real.sqrt q.beta:=by nlinarith [hd.1,hlam.1]
    have hl : -(2*Real.sqrt q.beta)≤1+q.beta-lam:=by nlinarith [hd.2,hlam.2]
    nlinarith

theorem outside_damping_strict (q : Tuning)
    (h : ¬((1-Real.sqrt q.beta)^2≤q.x ∧ q.y≤(1+Real.sqrt q.beta)^2)) :
    Real.sqrt q.beta<q.rhoQ := by
  have hne : q.rhoQ≠Real.sqrt q.beta:=fun hh => h (q.damping_iff.mp hh)
  have hle : Real.sqrt q.beta≤q.rhoQ:=
    (sqrt_le_rootRadius (p:=1+q.beta-q.x) q.beta_nonneg).trans (le_max_left _ _)
  exact lt_of_le_of_ne hle hne.symm

end polyak.General.Tuning
