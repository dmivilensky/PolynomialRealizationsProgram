import polyak.FareyPlateau.FanAnalysis.Parameters
import polyak.FareyPlateau.FanAnalysis.DualJets
import polyak.FareyPlateau.FanAnalysis.PartialJets

/-! The finite tests of the fan proof are restrictions of jointly analytic
functions of the actual three coefficients and the fan displacement. -/
noncomputable section
namespace polyak.FareyPlateau.FanAnalysis.Parameters
open General Levels

def test (j k : ℕ) (n : ℤ) (e : Point → ℝ) (τ y : ℝ) (z : Point×ℝ) : ℝ :=
  constraint ((k : ℝ)-1) (correction j k n z.1)
    (fun δ => phase j k z.1 (e z.1) 1 δ)
    (fun δ => phase j k z.1 (e z.1) (-((k : ℝ)-1)) δ) z.2 (τ+y*z.2)

theorem analytic_test {j k : ℕ} {n : ℤ} {e : Point → ℝ}
    (he : ∀p, AnalyticAt ℝ e p) (τ y : ℝ) (z : Point×ℝ)
    (ha : Real.sin (omega j k+z.2)≠0)
    (hc : Real.sin (omega j k-((k : ℝ)-1)*z.2)≠0) :
    AnalyticAt ℝ (test j k n e τ y) z := by
  have hnear := analytic_phase he 1 z (by simpa only [one_mul] using ha)
  have hfar := analytic_phase he (-((k : ℝ)-1)) z (by convert hc using 1; congr 1; ring)
  have hθ : AnalyticAt ℝ (fun z : Point×ℝ => τ+y*z.2) z :=
    analyticAt_const.add (analyticAt_const.mul analyticAt_snd)
  have hw : AnalyticAt ℝ (fun z : Point×ℝ => (k : ℝ)-1+correction j k n z.1*z.2) z :=
    analyticAt_const.add (((analytic_correction j k n z.1).comp analyticAt_fst).mul analyticAt_snd)
  exact ((hw.mul ((Real.analyticAt_cos.comp hnear).sub
    (Real.analyticAt_cos.comp (hθ.sub hnear)))).add (Real.analyticAt_cos.comp hfar)).sub
    (Real.analyticAt_cos.comp ((analyticAt_const.mul hθ).add hfar))

def atomLag (j k : ℕ) (e : Point → ℝ) (h l : ℝ) (z : Point×ℝ) : ℝ :=
  lagPath (l*omega j k) (l*h) (fun δ => phase j k z.1 (e z.1) h δ) z.2

def dualTest (j k : ℕ) (n : ℤ) (e : Point → ℝ) (h : ℝ) (z : Point×ℝ) : ℝ :=
  (1-mix j k n z.1)*atomLag j k e h n z+
    mix j k n z.1*atomLag j k e h ((n : ℝ)+k) z

theorem analytic_atomLag {j k : ℕ} {e : Point → ℝ}
    (he : ∀p, AnalyticAt ℝ e p) (h l : ℝ) (z : Point×ℝ)
    (hs : Real.sin (omega j k+h*z.2)≠0) :
    AnalyticAt ℝ (atomLag j k e h l) z := by
  have hphase := analytic_phase he h z hs
  exact (Real.analyticAt_cos.comp hphase).sub
    (Real.analyticAt_cos.comp ((analyticAt_const.add (analyticAt_const.mul analyticAt_snd)).sub hphase))

theorem analytic_dualTest {j k : ℕ} {n : ℤ} {e : Point → ℝ}
    (he : ∀p, AnalyticAt ℝ e p) (h : ℝ) (z : Point×ℝ)
    (hs : Real.sin (omega j k+h*z.2)≠0) :
    AnalyticAt ℝ (dualTest j k n e h) z := by
  have ht := (analytic_mix j k n z.1).comp analyticAt_fst
  exact ((analyticAt_const.sub ht).mul (analytic_atomLag he h n z hs)).add
    (ht.mul (analytic_atomLag he h ((n : ℝ)+k) z hs))

variable {q : Tuning} {j k : ℕ} (A : Edge.AdjacentData q j k)

theorem test_actual (e : Point → ℝ) (τ y δ : ℝ) :
    test j k A.lower e τ y (coordinates q,δ)=
      Actual.phi A (e (coordinates q)) δ (τ+y*δ) := by
  unfold test Actual.phi
  rw [correction_actual A]
  congr 2
  · funext d
    exact phase_actual A _ _ _
  · funext d
    exact phase_actual A _ _ _

theorem atomLag_actual (e : Point → ℝ) (h l δ : ℝ) :
    atomLag j k e h l (coordinates q,δ)=
      lagPath (l*A.frequency) (l*h) (anglePath q A.edgeShift A.frequency h (e (coordinates q))) δ := by
  unfold atomLag
  congr 1
  funext d
  exact phase_actual A _ _ _

theorem dualTest_actual (e : Point → ℝ) (h δ : ℝ) :
    dualTest j k A.lower e h (coordinates q,δ)=
      Actual.dualPath A (anglePath q A.edgeShift A.frequency h (e (coordinates q))) h δ := by
  unfold dualTest Actual.dualPath
  rw [mix_actual A,atomLag_actual A,atomLag_actual A]
  simp only [Edge.AdjacentData.upper,Int.cast_add,Int.cast_natCast]

end polyak.FareyPlateau.FanAnalysis.Parameters
