import polyak.ModeLocking.TwoLag.Lift

/-! E1 implies the primary finite-zero hypotheses required by compact
perturbation, including the endpoint and all first jets. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open General Levels Set Filter
open scoped Topology

theorem extension_zero_endpoint (q : Tuning) (s : ℝ) (K : ℕ) (a b : ℝ) :
    extension q s K a b 0=0 := by
  change extension q s K a b (frequencyZero : ℝ)=0
  rw [extension_actual]
  simp only [Curve.lag_at_zero, mul_zero, add_zero]

theorem extension_slope_endpoint (q : Tuning) (s : ℝ) (K : ℕ) (a b : ℝ) :
    deriv (extension q s K a b) 0=0 := by
  unfold extension
  rw [deriv_fun_add
    ((analyticAt_lagExtension q s 1 ⟨le_rfl, Real.pi_pos.le⟩).differentiableAt.const_mul a)
    ((analyticAt_lagExtension q s (-(K : ℤ)) ⟨le_rfl, Real.pi_pos.le⟩).differentiableAt.const_mul b)]
  simp only [deriv_const_mul_field, lagExtension_deriv_zero, mul_zero, add_zero]

namespace ExactData
variable {q : Tuning} {s : ℝ} {K L : ℕ} (D : ExactData q s K L)

def zeros : Finset ℝ := {0,(D.u 0 : ℝ),(D.u 1 : ℝ)}

theorem zeros_nonempty : D.zeros.Nonempty := ⟨0, by simp [zeros]⟩

theorem zeros_subset : ∀z∈D.zeros,z∈Icc 0 Real.pi := by
  intro z hz
  simp only [zeros, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl|rfl|rfl
  · exact ⟨le_rfl,Real.pi_pos.le⟩
  · exact (D.u 0).property
  · exact (D.u 1).property

theorem values_zero : ∀z∈D.zeros,extension q s K D.a D.b z=0 := by
  intro z hz
  simp only [zeros, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl|rfl|rfl
  · exact extension_zero_endpoint q s K D.a D.b
  · exact D.extension_zero 0
  · exact D.extension_zero 1

theorem slopes_zero : ∀z∈D.zeros,deriv (extension q s K D.a D.b) z=0 := by
  intro z hz
  simp only [zeros, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl|hz|hz
  · exact extension_slope_endpoint q s K D.a D.b
  all_goals
    subst z
    apply IsLocalMax.deriv_eq_zero
    filter_upwards [Ioo_mem_nhds (D.interior _).1 (D.interior _).2] with x hx
    rw [D.extension_zero]
    exact D.nonpos x ⟨hx.1.le,hx.2.le⟩

theorem curvature_negative : ∀z∈D.zeros,iteratedDeriv 2 (extension q s K D.a D.b) z<0 := by
  intro z hz
  simp only [zeros, Finset.mem_insert, Finset.mem_singleton] at hz
  simp only [iteratedDeriv_eq_iterate]
  rcases hz with rfl|rfl|rfl
  · exact D.endpoint_curv
  · exact D.curv 0
  · exact D.curv 1

theorem extension_pi_negative : extension q s K D.a D.b Real.pi<0 := by
  change extension q s K D.a D.b (frequencyPi : ℝ)<0
  rw [extension_actual]
  have h1 : (Geometry.shiftedCurve q s).lag 1 frequencyPi=-2 := by
    rw [Curve.lag_at_pi]
    norm_num
  rw [h1]
  have hK := mul_nonpos_of_nonneg_of_nonpos D.b_pos.le
    ((Geometry.shiftedCurve q s).lag_at_pi_nonpos (-(K : ℤ)))
  nlinarith [D.a_pos]

theorem strict_off_zeros (x : ℝ) (hx : x∈Icc 0 Real.pi) (hz : x∉D.zeros) :
    extension q s K D.a D.b x<0 := by
  have hx0 : 0<x := lt_of_le_of_ne hx.1 (by intro he;exact hz (by simp [zeros,←he]))
  rcases eq_or_lt_of_le hx.2 with hpi|hpi
  · simpa only [hpi] using D.extension_pi_negative
  · apply lt_of_le_of_ne (D.nonpos x hx)
    intro he
    have hzero := (D.zero_set x ⟨hx0,hpi⟩).mp he
    rcases hzero with rfl|rfl <;> exact hz (by simp [zeros])

end ExactData
end polyak.ModeLocking.TwoLag
