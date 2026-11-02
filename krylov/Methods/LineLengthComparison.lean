import krylov.Reference.CG
import krylov.LinearAlgebra.QuotientComparison
import Mathlib.Analysis.InnerProductSpace.Continuous
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), actual informed line quotient comparison.
Use: transfer genuine observed virtual-field differences through the real
known-curvature line length, deriving its denominator domain from the limit.
Source: actual inner-product comparison and real reciprocal continuity.
-/

namespace krylov.Methods
noncomputable section
open Filter Topology Asymptotics krylov.LinearAlgebra krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {α : Type*} {f : Filter α}

/-- The actual known-curvature line quotient preserves the genuine order
of its actual virtual-gradient and direction differences at a nonzero
true reference curvature, without a supplied quotient-error premise.
Use: compare the original history-only informed S policy with native D
fields on that same real execution.
Article: main_krylov, thm:local(a), actual known-curvature quotient order.
Proof: true field differences and native limits give the real recorded
limits. The exact bilinear difference estimate controls numerator and
curvature errors. The known operator preserves the direction error;
the proved genuine quotient comparison gives the real line-length order. -/
theorem lineLength_difference_order (Q : E →L[ℝ] E) (g d G D : α → E)
    (g0 d0 : E) (hg : Tendsto G f (𝓝 g0)) (hd : Tendsto D f (𝓝 d0))
    (hcurv : inner ℝ d0 (Q d0)≠0) (r : α → ℝ) (hr : Tendsto r f (𝓝 0))
    (hgd : (fun z => g z-G z) =O[f] r) (hdd : (fun z => d z-D z) =O[f] r) :
    (fun z => lineLength (g z) (d z) (Q (d z))-lineLength (G z) (D z) (Q (D z))) =O[f] r := by
  have hga : Tendsto g f (𝓝 g0) := by
    simpa only [sub_add_cancel,zero_add] using (hgd.trans_tendsto hr).add hg
  have hda : Tendsto d f (𝓝 d0) := by
    simpa only [sub_add_cancel,zero_add] using (hdd.trans_tendsto hr).add hd
  have hDb : D =O[f] (fun _ => (1 : ℝ)) := hd.isBigO_one ℝ
  have hgb : g =O[f] (fun _ => (1 : ℝ)) := hga.isBigO_one ℝ
  have hnum : (fun z => -inner ℝ (d z) (g z)-(-inner ℝ (D z) (G z))) =O[f] r := by
    exact (inner_difference_order d g D G r hdd hgd hDb hgb).neg_left.congr_left
      (fun z => by ring)
  have hQd : (fun z => Q (d z)-Q (D z)) =O[f] r := by
    simpa only [Function.comp_def,map_sub] using (Q.isBigO_comp (fun z => d z-D z) f).trans hdd
  have hQdb : (fun z => Q (d z)) =O[f] (fun _ => (1 : ℝ)) :=
    (Q.continuous.tendsto d0 |>.comp hda).isBigO_one ℝ
  have hden := inner_difference_order d (fun z => Q (d z)) D (fun z => Q (D z)) r hdd hQd hDb hQdb
  have hba : Tendsto (fun z => inner ℝ (d z) (Q (d z))) f (𝓝 (inner ℝ d0 (Q d0))) :=
    hda.inner (Q.continuous.tendsto d0 |>.comp hda)
  have hbd : Tendsto (fun z => inner ℝ (D z) (Q (D z))) f (𝓝 (inner ℝ d0 (Q d0))) :=
    hd.inner (Q.continuous.tendsto d0 |>.comp hd)
  have hcb : (fun z => -inner ℝ (D z) (G z)) =O[f] (fun _ => (1 : ℝ)) :=
    (hd.inner hg).neg.isBigO_one ℝ
  exact quotient_difference_order _ _ _ _ r _ _ hcurv hcurv hba hbd hcb hnum hden

end
end krylov.Methods
