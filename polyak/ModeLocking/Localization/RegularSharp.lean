import polyak.ModeLocking.Localization.SharpPotential
import polyak.ModeLocking.Localization.SupportPenalty
import polyak.ModeLocking.Localization.PeriodDistance
import polyak.ModeLocking.Regular.Threshold

/-! The sharp coefficient is the minimum of the actual second-order jets,
and controls every sufficiently close competing periodic grid. -/
noncomputable section
namespace polyak.ModeLocking.Localization
open Levels MeasureTheory Set Metric Filter
open scoped Topology BigOperators
variable {q : General.Tuning} {t : ℝ} {L : ℕ}

def regularSupport (D : RegularData q t L) : Finset ℝ :=
  Finset.univ.image (fun i => (D.atoms i:ℝ))

theorem regularSupport_nonempty (D : RegularData q t L) : (regularSupport D).Nonempty :=
  ⟨D.atoms ⟨0,D.d_pos⟩,Finset.mem_image.mpr ⟨⟨0,D.d_pos⟩,Finset.mem_univ _,rfl⟩⟩

def lockingCoefficient (D : RegularData q t L) (i : Fin D.d) : ℝ :=
  |deriv^[2] (finiteSymbol q t D.lags D.dual) (D.atoms i:ℝ)| /
    (2*Real.sin (Geometry.shiftedCurve q t (D.atoms i))*pinningPolynomial D.lags D.dual (D.atoms i))

theorem regularIndex_nonempty (D : RegularData q t L) :
    (Finset.univ : Finset (Fin D.d)).Nonempty := ⟨⟨0,D.d_pos⟩,Finset.mem_univ _⟩

def minimalLockingCoefficient (D : RegularData q t L) : ℝ :=
  (Finset.univ : Finset (Fin D.d)).inf' (regularIndex_nonempty D) (lockingCoefficient D)

theorem lockingCoefficient_pos (D : RegularData q t L) (i : Fin D.d) :
    0 < lockingCoefficient D i := by
  apply div_pos (abs_pos.mpr (D.support_curvature i).ne)
  exact mul_pos (mul_pos (by norm_num) (phase_sin_pos q t (D.atoms i)
    ⟨(D.atoms_grid i).1,D.atoms_lt_pi i⟩)) (D.pinning_pos i)

theorem minimalLockingCoefficient_pos (D : RegularData q t L) :
    0 < minimalLockingCoefficient D := by
  unfold minimalLockingCoefficient
  rw [Finset.lt_inf'_iff]
  intro i _
  exact lockingCoefficient_pos D i

theorem minimalLockingCoefficient_le (D : RegularData q t L) (i : Fin D.d) :
    minimalLockingCoefficient D ≤ lockingCoefficient D i :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem continuousOn_extendedPotential (D : RegularData q t L) :
    ContinuousOn (extendedPotential D) (Ioo 0 Real.pi) := by
  intro x hx
  have hc := (analyticAt_finiteSymbol q t D.lags D.dual ⟨hx.1.le,hx.2.le⟩).continuousAt
  have hP : Continuous (pinningPolynomial D.lags D.dual) := by
    unfold pinningPolynomial
    fun_prop
  have hs := Real.continuous_sin.continuousAt.comp
    (continuousAt_extendedPhase q t x ⟨hx.1.le,hx.2.le⟩)
  apply (hc.neg.div (hs.mul hP.continuousAt) ?_).continuousWithinAt
  dsimp only [Pi.mul_apply,Function.comp_def]
  rw [Geometry.jointAngle_actual q t ⟨hx.1.le,hx.2.le⟩]
  exact (mul_pos (Real.sin_pos_of_pos_of_lt_pi (Geometry.shiftedAngle_mem q t hx).1
    (Geometry.shiftedAngle_mem q t hx).2)
    (regular_pinning_pos D ⟨x,hx.1.le,hx.2.le⟩ hx.1)).ne'

theorem regular_sharp_potential_penalty (D : RegularData q t L) (ε : ℝ)
    (hε : 0 < ε) (hεc : ε < minimalLockingCoefficient D) :
    ∃ δ > 0, ∀ d, 0 < d → d < δ → ∀ ω ∈ Ioo (0:ℝ) Real.pi,
      d ≤ infDist ω (regularSupport D:Set ℝ) →
      (minimalLockingCoefficient D-ε)*d^2 ≤ extendedPotential D ω := by
  have hpos : ∀ x ∈ Ioo (0:ℝ) Real.pi, x ∉ regularSupport D → 0 < extendedPotential D x := by
    intro x hx hnot
    let ω : Frequency := ⟨x,hx.1.le,hx.2.le⟩
    rw [extendedPotential_actual D ω]
    apply regularPotential_pos D ω hx
    intro i hi
    exact hnot (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,congrArg Subtype.val hi.symm⟩)
  have hlocal : ∀ z ∈ regularSupport D, ∃ r > 0, ∀ x, |x-z| < r →
      (minimalLockingCoefficient D-ε)*(x-z)^2 ≤ extendedPotential D x := by
    intro z hz
    obtain ⟨i,_hi,rfl⟩ := Finset.mem_image.mp hz
    apply quadratic_lower_of_limit
    · rw [extendedPotential_actual D (D.atoms i),regularPotential_zero D i]
    · exact potential_quadratic_limit D i
    · change minimalLockingCoefficient D-ε < lockingCoefficient D i
      have hh := minimalLockingCoefficient_le D i
      linarith
  exact sharp_potential_penalty (regularSupport_nonempty D) (sub_pos.mpr hεc)
    (continuousOn_extendedPotential D) hpos (regularPotential_tendsto_at_zero D)
      (regularPotential_tendsto_at_pi D) hlocal

end polyak.ModeLocking.Localization
