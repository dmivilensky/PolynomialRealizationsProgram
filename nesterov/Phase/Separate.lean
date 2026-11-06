import nesterov.Phase.LagOne
import nesterov.Quadratic.ScalarRoots
import nesterov.Quadratic.ScaledJury
import nesterov.Momentum.QuadraticDictionary

/-! Lemma `lem:separate`: a positive lag-one circle separates every scalar
quadratic mode; continuity of the actual maximal root modulus propagates the
interior condition from μ to the whole curvature interval. -/
noncomputable section
open Set
namespace nesterov.Quadratic

theorem continuous_rootRadius : Continuous (fun x : ℝ×ℝ=>polyak.General.rootRadius x.1 x.2) := by
  unfold polyak.General.rootRadius
  apply Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  intro x hx
  have hd : x.1^2-4*x.2=0 := by linarith
  rw [hd,Real.sqrt_zero,add_zero]
  have hq : x.2=(x.1/2)^2 := by nlinarith
  rw [hq,Real.sqrt_sq_eq_abs,abs_div]
  norm_num

theorem continuous_scalarRadius (β τ h : ℝ) : Continuous (scalarRadius β τ h) := by
  exact continuous_rootRadius.comp (show Continuous (fun lam=>(S β τ h lam,Q β τ h lam)) by
    unfold S Q
    fun_prop)

theorem characteristic_affine (β τ h μ L lam : ℝ) (z : ℂ) :
    ((L-μ:ℝ):ℂ)*characteristic β τ h lam z=
      ((L-lam:ℝ):ℂ)*characteristic β τ h μ z+
        ((lam-μ:ℝ):ℂ)*characteristic β τ h L z := by
  simp only [characteristic,Complex.ofReal_sub,Complex.ofReal_mul]
  ring
end nesterov.Quadratic

namespace nesterov.Phase

/-- The affine family cannot have a circle root under the strictly positive
lag-one symbol. Endpoint curvatures and real circle points are included. -/
theorem no_root_on_circle_of_lagOne {μ L β τ h r : ℝ} (_hμL : μ<L) (hr : r<1)
    (hpos : ∀ z : ℂ,‖z‖=r →
      0<((1-z)*Quadratic.characteristic β τ h μ z*
        star (Quadratic.characteristic β τ h L z)).re)
    {lam : ℝ} (hlam : lam∈Icc μ L) {z : ℂ} (hz : ‖z‖=r) :
    Quadratic.characteristic β τ h lam z≠0 := by
  intro hroot
  let A := Quadratic.characteristic β τ h μ z
  let B := Quadratic.characteristic β τ h L z
  have he : ((L-lam:ℝ):ℂ)*A+((lam-μ:ℝ):ℂ)*B=0 := by
    rw [←Quadratic.characteristic_affine,hroot,mul_zero]
  have hP := hpos z hz
  change 0<((1-z)*A*star B).re at hP
  by_cases hlast : lam=L
  · subst lam
    have hB : B=0 := hroot
    simp [hB] at hP
  have ha : 0<L-lam := sub_pos.mpr (lt_of_le_of_ne hlam.2 hlast)
  have hb : 0≤lam-μ := sub_nonneg.mpr hlam.1
  have he' := congrArg (fun w : ℂ=>w*star B) he
  have hreal := congrArg Complex.re he'
  have himag := congrArg Complex.im he'
  have hBB : B*star B=(Complex.normSq B:ℂ) := Complex.mul_conj B
  simp only [add_mul,mul_assoc,hBB,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,mul_zero,sub_zero,Complex.zero_re] at hreal
  simp only [add_mul,mul_assoc,hBB,Complex.add_im,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,mul_zero,add_zero,Complex.zero_im] at himag
  change (L-lam)*(A*star B).re+(lam-μ)*Complex.normSq B=0 at hreal
  have him : (A*star B).im=0 := (mul_eq_zero.mp himag).resolve_left ha.ne'
  have hre : (A*star B).re≤0 := by
    nlinarith [Complex.normSq_nonneg B]
  have hzre : z.re<1 := (Complex.re_le_norm z).trans_lt (hz.trans_lt hr)
  have heP : ((1-z)*A*star B).re=(1-z.re)*(A*star B).re := by
    rw [mul_assoc]
    simp only [Complex.mul_re,Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,him,mul_zero,sub_zero]
  rw [heP] at hP
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (sub_pos.mpr hzre).le hre)) hP

/-- The actual maximal root modulus varies continuously with curvature and
cannot cross a circle containing no scalar quadratic root. -/
theorem scalarRadius_lt_of_no_circle {μ L β τ h r : ℝ}
    (_hμL : μ<L)
    (hnoroot : ∀ lam∈Icc μ L,∀ z : ℂ,‖z‖=r → Quadratic.characteristic β τ h lam z≠0)
    (hμroot : ∀ z : ℂ,Quadratic.characteristic β τ h μ z=0 → ‖z‖<r)
    {lam : ℝ} (hlam : lam∈Icc μ L) : Quadratic.scalarRadius β τ h lam<r := by
  have hstart : Quadratic.scalarRadius β τ h μ<r := by
    obtain ⟨z,hz,he⟩ := (Quadratic.scalarRadius_isGreatest β τ h μ).1
    rw [he]
    exact hμroot z hz
  by_contra hnot
  have hcont : ContinuousOn (Quadratic.scalarRadius β τ h) (Icc μ lam) :=
    (Quadratic.continuous_scalarRadius β τ h).continuousOn
  obtain ⟨lam',hlam',he⟩ := intermediate_value_Icc hlam.1 hcont
    (show r∈Icc (Quadratic.scalarRadius β τ h μ) (Quadratic.scalarRadius β τ h lam) from
      ⟨hstart.le,le_of_not_gt hnot⟩)
  obtain ⟨z,hz,hze⟩ := (Quadratic.scalarRadius_isGreatest β τ h lam').1
  exact hnoroot lam' ⟨hlam'.1,hlam'.2.trans hlam.2⟩ z (hze.symm.trans he) hz

/-- Lemma separate: positivity plus the μ-endpoint interior condition imply
the strict quadratic maximum bound, with no prior stability assumption. -/
theorem quadraticRate_lt_of_lagOne {μ L β τ h r : ℝ}
    (hμL : μ<L) (hr : r<1)
    (hpos : ∀ z : ℂ,‖z‖=r →
      0<((1-z)*Quadratic.characteristic β τ h μ z*
        star (Quadratic.characteristic β τ h L z)).re)
    (hμroot : ∀ z : ℂ,Quadratic.characteristic β τ h μ z=0 → ‖z‖<r) :
    Quadratic.quadraticRate μ L β τ h<r := by
  obtain ⟨lam,hlam,z,hz,he⟩ := (Quadratic.quadraticRate_isGreatest_general hμL.le).1
  rw [he]
  exact ((Quadratic.scalarRadius_isGreatest β τ h lam).2 ⟨z,hz,rfl⟩).trans_lt
    (scalarRadius_lt_of_no_circle hμL
      (fun _ hlam _ hz=>no_root_on_circle_of_lagOne hμL hr hpos hlam hz) hμroot hlam)

/-- All conclusions of Lemma separate, on the literal tuning and actual
uniform all-Hilbert rate. Stability and the middle-radius condition are
consequences, rather than additional assumptions. -/
theorem separate (q : Momentum.Tuning) {μ L r : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (hr : r∈Ioo (0:ℝ) 1)
    (hpos : ∀ z : ℂ,‖z‖=r →
      0<((1-z)*Quadratic.characteristic q.beta q.tau q.stepSize μ z*
        star (Quadratic.characteristic q.beta q.tau q.stepSize L z)).re)
    (hμroot : ∀ z : ℂ,Quadratic.characteristic q.beta q.tau q.stepSize μ z=0 → ‖z‖<r) :
    Quadratic.quadraticRate μ L q.beta q.tau q.stepSize<r ∧
      q.Stable μ L ∧
      IQC.middleRadius (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne') μ L<r ∧
      Momentum.momentumRate q.beta q.tau q.stepSize q.step_pos.ne' μ L<r := by
  have hq:=quadraticRate_lt_of_lagOne hμL hr.2 hpos hμroot
  have hstable : q.Stable μ L:=
    (Quadratic.stable_iff_quadraticRate_lt_one hμL.le).mpr (hq.trans hr.2)
  have hmid : IQC.middleRadius (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne') μ L<r := by
    have hm:=IQC.middleRadius_le_quadraticRate
      (Momentum.method q.beta q.tau q.stepSize q.step_pos.ne') hμ hμL
    rw [Momentum.quadraticRate_method] at hm
    exact hm.trans_lt hq
  have he : Real.exp (Real.log r)=r:=Real.exp_log hr.1
  have hrate:=momentumRate_lt_of_lagOne q hμ hμL
    (t:=Real.log r) (Real.log_nonpos hr.1.le hr.2.le)
    (by rwa [he]) (by simpa only [he] using hpos)
  rw [he] at hrate
  exact ⟨hq,hstable,hmid,hrate⟩

end nesterov.Phase
