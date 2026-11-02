import jacobi.Analytic.PersymmetricEnergy
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
Article: jacobi, Theorem 4.2.
The article's original persymmetric constant is real analytic on the
entire admissible order interval. This follows from the proved genuine
holomorphic profile integral, with exact original real restriction.
Use: states the original order-analyticity theorem with a fixed real function rather than a proof-dependent parameter.
-/
namespace jacobi.Analytic
noncomputable section
open Set Metric Filter jacobi.GelfandLevitan
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The original persymmetric constant as a real function on the admissible open order interval.
Use: states the original order-analyticity theorem with a fixed real function rather than a proof-dependent parameter.
Article: jacobi, Theorem 4.2.
The value zero outside alpha>-1 only totalizes the Lean function; the theorem concerns the original admissible interval. -/
def originalPersymmetricEnergy (a : ℝ) : ℝ :=
  if ha : -1<a then persymmetricConstant a ha else 0

/-- On the admissible interval the real energy function is exactly the original article constant.
Use: transfers real analyticity to the previously constructed original squared-profile energy without changing its definition or normalization.
Article: jacobi, Theorem 4.2.
Proof: select the genuine admissible branch of the totalized source function. -/
theorem originalPersymmetricEnergy_eq {a : ℝ} (ha : -1<a) :
    originalPersymmetricEnergy a=persymmetricConstant a ha := by
  simp only [originalPersymmetricEnergy,dite_eq_left ha]

/-- The article's original persymmetric constant is real analytic at every admissible order.
Use: supplies the exact real-analytic conclusion of Theorem 4.2, before its separate contact and optimal-energy derivative assertions.
Article: jacobi, Theorem 4.2.
Proof: obtain the proved actual holomorphic energy continuation on a genuine order disk. Restrict its real part to the real axis by the community analytic restriction theorem. Its proved original real identification agrees with the source energy throughout a real neighborhood, so real analyticity transfers to that same original function. -/
theorem originalPersymmetricEnergy_analyticAt {a0 : ℝ} (ha0 : -1<a0) :
    AnalyticAt ℝ originalPersymmetricEnergy a0 := by
  -- The analytic extension is the actual norm-summed source profile and its genuine squared integral.
  obtain ⟨D,r,C,hr,_,_,_,_,_,_,hE,hreal⟩ := analytic_persymmetric_energy ha0
  have he := (hE.analyticOnNhd isOpen_ball (a0:ℂ) (mem_ball_self hr)).re_ofReal
  apply he.congr
  filter_upwards [Ioi_mem_nhds ha0,ball_mem_nhds a0 hr] with b hb hbr
  have hbd : ‖(b:ℂ)-(a0:ℂ)‖≤r := by
    rw [← _root_.Complex.ofReal_sub,_root_.Complex.norm_real,Real.norm_eq_abs]
    simpa only [mem_ball,Real.dist_eq] using (mem_ball.mp hbr).le
  rw [(hreal b hb hbd).2,_root_.Complex.ofReal_re,originalPersymmetricEnergy_eq hb]

/-- The article's original persymmetric constant is real analytic throughout its full admissible open order interval.
Use: the global order regularity assertion in Theorem 4.2 is unconditional on all alpha>-1.
Article: jacobi, Theorem 4.2.
Proof: apply the proved actual energy analyticity at each point of the original open interval. -/
theorem originalPersymmetricEnergy_realAnalytic :
    AnalyticOnNhd ℝ originalPersymmetricEnergy (Ioi (-1)) :=
  fun _ ha => originalPersymmetricEnergy_analyticAt ha

end
end jacobi.Analytic
