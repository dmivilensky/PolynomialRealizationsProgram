import nesterov.Flow.QuadraticRates
import nesterov.Flow.Existence

/-!
Article: Theorem `flow`(d), the literal infima over genuine Hilbert-space
solutions and over all finite global smoothness bounds.
-/

namespace nesterov.Flow

noncomputable section

/-- One nonstationary actual heavy-ball solution in an arbitrary real Hilbert
space.  This follows the universe convention of `nesterov.Rates.HilbertRun`.
The lower bounds themselves remain universe-polymorphic. -/
structure Run (θ m : ℝ) where
  Carrier : Type
  [normed : NormedAddCommGroup Carrier]
  [inner : InnerProductSpace ℝ Carrier]
  [complete : CompleteSpace Carrier]
  f : Carrier → ℝ
  objective : Objective m f
  x : ℝ → Carrier
  v : ℝ → Carrier
  solution : IsSolution θ f x v
  nontrivial : ‖x 0‖ + ‖v 0‖ ≠ 0

attribute [instance] Run.normed Run.inner Run.complete

structure SmoothRun (θ m : ℝ) extends Run θ m where
  L : ℝ
  smooth : polyak.CenteredSmoothStronglyConvex m L f

def Run.stateExponent {θ m : ℝ} (r : Run θ m) : EReal := decayExponent r.x r.v

def Run.valueExponent {θ m : ℝ} (r : Run θ m) : EReal :=
  observableExponent (fun t => r.f (r.x t))

def Run.energyExponent {θ m : ℝ} (r : Run θ m) : EReal :=
  observableExponent (fun t => energy r.f (r.x t) (r.v t))

def worstStateExponent (θ m : ℝ) : EReal := sInf (Set.range (Run.stateExponent (θ := θ) (m := m)))

def worstValueExponent (θ m : ℝ) : EReal := sInf (Set.range (Run.valueExponent (θ := θ) (m := m)))

def worstEnergyExponent (θ m : ℝ) : EReal := sInf (Set.range (Run.energyExponent (θ := θ) (m := m)))

def worstSmoothStateExponent (θ m : ℝ) : EReal :=
  sInf (Set.range (fun r : SmoothRun θ m => r.toRun.stateExponent))

def worstSmoothValueExponent (θ m : ℝ) : EReal :=
  sInf (Set.range (fun r : SmoothRun θ m => r.toRun.valueExponent))

def worstSmoothEnergyExponent (θ m : ℝ) : EReal :=
  sInf (Set.range (fun r : SmoothRun θ m => r.toRun.energyExponent))

theorem universal_inf_lower {θ m : ℝ} (hθ : 0 < θ) :
    (cF θ m : EReal) ≤ worstStateExponent θ m ∧
      ((2 * cF θ m : ℝ) : EReal) ≤ worstValueExponent θ m ∧
      ((2 * cF θ m : ℝ) : EReal) ≤ worstEnergyExponent θ m := by
  refine ⟨le_sInf ?_, le_sInf ?_, le_sInf ?_⟩
  · rintro _ ⟨r, rfl⟩
    exact r.solution.cF_le_decayExponent hθ r.objective
  · rintro _ ⟨r, rfl⟩
    exact (r.solution.value_energy_exponents_ge hθ r.objective).1
  · rintro _ ⟨r, rfl⟩
    exact (r.solution.value_energy_exponents_ge hθ r.objective).2

theorem universal_inf_le_smooth (θ m : ℝ) :
    worstStateExponent θ m ≤ worstSmoothStateExponent θ m ∧
      worstValueExponent θ m ≤ worstSmoothValueExponent θ m ∧
      worstEnergyExponent θ m ≤ worstSmoothEnergyExponent θ m := by
  refine ⟨le_sInf ?_, le_sInf ?_, le_sInf ?_⟩
  · rintro _ ⟨r, rfl⟩
    exact sInf_le ⟨r.toRun, rfl⟩
  · rintro _ ⟨r, rfl⟩
    exact sInf_le ⟨r.toRun, rfl⟩
  · rintro _ ⟨r, rfl⟩
    exact sInf_le ⟨r.toRun, rfl⟩

theorem exists_quadratic_smoothRun {θ m : ℝ} (hθ : 0 < θ) (hm : 0 < m) :
    ∃ r : SmoothRun θ m, r.toRun.stateExponent = (cQ θ m : EReal) ∧
      r.toRun.valueExponent = ((2 * cQ θ m : ℝ) : EReal) ∧
      r.toRun.energyExponent = ((2 * cQ θ m : ℝ) : EReal) := by
  obtain ⟨x, v, hsol, hnorm, hstate, hvalue, henergy⟩ := exists_quadratic_all_exponents hθ hm
  have hq := quadratic_objective (E := ℂ) hm (show m < m + 1 by linarith)
  let r : SmoothRun θ m :=
    { Carrier := ℂ
      f := fun z => m / 2 * ‖z‖ ^ 2
      objective := of_centeredSmoothStronglyConvex hq
      x := x
      v := v
      solution := hsol
      nontrivial := by rw [hnorm]; positivity
      L := m + 1
      smooth := hq }
  exact ⟨r, hstate, hvalue, henergy⟩

theorem quadratic_inf_upper {θ m : ℝ} (hθ : 0 < θ) (hm : 0 < m) :
    worstSmoothStateExponent θ m ≤ (cQ θ m : EReal) ∧
      worstSmoothValueExponent θ m ≤ ((2 * cQ θ m : ℝ) : EReal) ∧
      worstSmoothEnergyExponent θ m ≤ ((2 * cQ θ m : ℝ) : EReal) := by
  obtain ⟨r, hs, hv, he⟩ := exists_quadratic_smoothRun hθ hm
  exact ⟨sInf_le ⟨r, hs⟩, sInf_le ⟨r, hv⟩, sInf_le ⟨r, he⟩⟩

end
end nesterov.Flow
