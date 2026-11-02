import krylov.Stability.C1VanishingProduct
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(a), actual C-one cubic coefficient freezing.
Use: retain actual increments and the actual first-order vanishing input
while freezing only smooth outer coefficients in the native launch model.
Source: exact operator product differences and three actual first-order
vanishing factors, derived from primitive C-one data.
-/

namespace krylov.Stability
noncomputable section
open Filter Topology Asymptotics
variable {X V E F G : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Freezing only the true smooth outer coefficients around a genuinely
vanishing actual middle increment and actual vanishing input leaves a
cubic remainder, from primitive C-one data on the full parameter space.
Use: the known-base full-model output retains the actual increments and
actual incoming gradient without replacing either by a derivative.
Article: main_krylov, thm:local(a), native cubic launch remainder.
Proof: split the exact difference into its changed left and changed right
coefficient. Both terms have three actual first-order vanishing factors;
the remaining coefficients are genuinely bounded by continuity. -/
theorem c1_vanishing_input_freeze_remainder
    (L : X → F →L[ℝ] G) (D : X → E →L[ℝ] F) (B : X → V →L[ℝ] E) (g : X → V)
    (hL : DifferentiableAt ℝ L 0) (hD : DifferentiableAt ℝ D 0)
    (hB : DifferentiableAt ℝ B 0) (hg : DifferentiableAt ℝ g 0)
    (hD0 : D 0=0) (hg0 : g 0=0) :
    (fun z => L z (D z (B z (g z)))-L 0 (D z (B 0 (g z))))
      =O[𝓝 0] (fun z => ‖z‖^3) := by
  have hLs : (fun z => L z-L 0) =O[𝓝 0] (fun z => ‖z‖) := by
    simpa only [sub_zero] using hL.isBigO_sub.norm_right
  have hDs : D =O[𝓝 0] (fun z => ‖z‖) := by
    simpa only [hD0,sub_zero] using hD.isBigO_sub.norm_right
  have hBs : (fun z => B z-B 0) =O[𝓝 0] (fun z => ‖z‖) := by
    simpa only [sub_zero] using hB.isBigO_sub.norm_right
  have hgs : g =O[𝓝 0] (fun z => ‖z‖) := by
    simpa only [hg0,sub_zero] using hg.isBigO_sub.norm_right
  have hBb : B =O[𝓝 0] (fun _ => (1 : ℝ)) := hB.continuousAt.tendsto.isBigO_one ℝ
  have hfirst := clm_apply_bigO (fun z => L z-L 0) _ _ _ hLs
    (clm_apply_bigO D _ _ _ hDs (clm_apply_bigO B g _ _ hBb hgs))
  have hsecond := (L 0).isBigO_comp _ (𝓝 0) |>.trans
    (clm_apply_bigO D _ _ _ hDs (clm_apply_bigO (fun z => B z-B 0) g _ _ hBs hgs))
  have h1 : (fun z => (L z-L 0) (D z (B z (g z)))) =O[𝓝 0] (fun z => ‖z‖^3) :=
    hfirst.congr_right (fun z => by ring)
  have h2 : (fun z => L 0 (D z ((B z-B 0) (g z)))) =O[𝓝 0] (fun z => ‖z‖^3) :=
    hsecond.congr_right (fun z => by ring)
  exact (h1.add h2).congr_left (fun z => by
    simp only [_root_.sub_apply,map_sub]
    abel)

end
end krylov.Stability
