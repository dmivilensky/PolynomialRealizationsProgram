import polyak.ModeLocking.TwoLag.Pinning
import polyak.ModeLocking.TwoLag.SecondJet
import polyak.ModeLocking.TwoLag.Endpoint

/-! Genuine analytic real-frequency extensions of the two-lag symbol. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open General Levels Set Filter
open scoped Topology

def phase (q : Tuning) (s x : ℝ) : ℝ :=
  Geometry.jointAngle ![q.kappa,q.y,q.beta,s,x]

theorem analyticAt_phase (q : Tuning) (s : ℝ) {x : ℝ} (hx : x∈Icc 0 Real.pi) :
    AnalyticAt ℝ (phase q s) x := by
  have hm : AnalyticAt ℝ (fun y : ℝ => ![q.kappa,q.y,q.beta,s,y]) x := by
    apply AnalyticAt.pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact (Geometry.analyticAt_jointAngle_actual q s hx).comp (f := fun y : ℝ => ![q.kappa,q.y,q.beta,s,y]) hm

theorem analyticAt_lagExtension (q : Tuning) (s : ℝ) (n : ℤ) {x : ℝ}
    (hx : x∈Icc 0 Real.pi) : AnalyticAt ℝ (lagExtension q s n) x := by
  have hp := analyticAt_phase q s hx
  exact (Real.analyticAt_cos.comp hp).sub
    (Real.analyticAt_cos.comp ((analyticAt_const.mul analyticAt_id).sub hp))

def extension (q : Tuning) (s : ℝ) (K : ℕ) (a b : ℝ) (x : ℝ) : ℝ :=
  a*lagExtension q s 1 x+b*lagExtension q s (-(K : ℤ)) x

theorem analyticAt_extension (q : Tuning) (s : ℝ) (K : ℕ) (a b : ℝ)
    {x : ℝ} (hx : x∈Icc 0 Real.pi) : AnalyticAt ℝ (extension q s K a b) x :=
  (analyticAt_const.mul (analyticAt_lagExtension q s 1 hx)).add
    (analyticAt_const.mul (analyticAt_lagExtension q s (-(K : ℤ)) hx))

theorem extension_actual (q : Tuning) (s : ℝ) (K : ℕ) (a b : ℝ) (ω : Frequency) :
    extension q s K a b ω = a*(Geometry.shiftedCurve q s).lag 1 ω+
      b*(Geometry.shiftedCurve q s).lag (-(K : ℤ)) ω := by
  simp only [extension, lagExtension_actual]

end polyak.ModeLocking.TwoLag
