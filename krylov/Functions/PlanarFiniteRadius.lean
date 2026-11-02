import krylov.Functions.PlanarEuclideanGradient
import krylov.LinearAlgebra.InformationRadius

/-!
Article: main_krylov, thm:Fplanar and prop:Fcycle(iii), genuine finite-scale
cubic information radius. Use: retain the exact Euclidean leading coefficient
for every unrestricted common output of two actual indistinguishable cubic
functions. Source: exact last-point Hessians, the actual fourth-order gradient
remainder, and the elementary two-scenario half-distance inequality.
-/
namespace krylov.Functions
noncomputable section
open krylov.Tensor.BinaryCubic
open scoped InnerProductSpace

/-- The actual unit-scale last-point Hessian perturbation of the full planar family.
Article: main_krylov, thm:Fplanar and prop:Fcycle(iii). -/
def planeTerminalOperator (r : ℝ) (t : krylov.Tensor.BinaryCubic) : Plane →L[ℝ] Plane :=
  (EuclideanSpace.proj 0).smulRight (planeOfPair (t.t0/2+r*t.t1,t.t1/2+r*t.t2))+
  (EuclideanSpace.proj 1).smulRight (planeOfPair (t.t1/2+r*t.t2,r*t.t3/2))

/-- The genuine common post-search gradient coefficient.
Article: main_krylov, thm:Fplanar. -/
def planeTerminalRho (r : ℝ) (t : krylov.Tensor.BinaryCubic) : Plane :=
  planeOfPair (r/2*(t.t1+r*t.t2),0)

/-- The true terminal model has its exact scale-separated operator formula.
Article: main_krylov, thm:Fplanar. -/
theorem planeTerminalModel_eq (p r : ℝ) (t : krylov.Tensor.BinaryCubic) (v : ℝ × ℝ) :
    planeOfPair (planarCubicTerminalModel p r t v)=
      p^2 • planeTerminalRho r t+planeOfPair v+p • planeTerminalOperator r t (planeOfPair v) := by
  rw [planarCubicTerminalModel,planarCubicGradient_last,planeOfPair_add,planeOfPair_add]
  ext i
  fin_cases i <;>
    simp [planeTerminalRho,planeTerminalOperator,planeOfPair,planarValueCoordinateHessianAction,
      ContinuousLinearMap.smulRight_apply] <;> ring

/-- Equal true observations give exactly the same real post-search gradient.
Article: main_krylov, thm:Fplanar. -/
theorem planeTerminalRho_eq (r : ℝ) (t u : krylov.Tensor.BinaryCubic)
    (hobs : observe r t=observe r u) : planeTerminalRho r t=planeTerminalRho r u := by
  have hp := congrArg Observation.P hobs
  unfold planeTerminalRho
  change planeOfPair (r/2*(observe r t).P,0)=planeOfPair (r/2*(observe r u).P,0)
  rw [hp]

/-- The actual two terminal Hessians have precisely the printed missing-C
leading information direction. Article: main_krylov, thm:Fplanar. -/
theorem planeTerminal_difference_rho (r : ℝ) (t u : krylov.Tensor.BinaryCubic)
    (hobs : observe r t=observe r u) :
    (planeTerminalOperator r u-planeTerminalOperator r t) (planeTerminalRho r t)=
      ((u.t2-t.t2)*r^2*(t.t1+r*t.t2)/4) • planarFibreDirection r := by
  have h0 := congrArg Observation.t0 hobs
  have hP := congrArg Observation.P hobs
  change t.t0=u.t0 at h0
  change t.t1+r*t.t2=u.t1+r*u.t2 at hP
  ext i
  fin_cases i
  · simp [planeTerminalOperator,planeTerminalRho,planeOfPair,planarFibreDirection,
      ContinuousLinearMap.smulRight_apply,h0]
    linear_combination -(r^2*(t.t1+r*t.t2)/2)*hP
  · simp [planeTerminalOperator,planeTerminalRho,planeOfPair,planarFibreDirection,
      ContinuousLinearMap.smulRight_apply,h0]
    linear_combination -(r*(t.t1+r*t.t2)/4)*hP

/-- The exact true twin information vector has the sharp printed binary-chord
norm. Article: main_krylov, thm:Fplanar. -/
theorem planeTerminal_information_norm (r : ℝ) (t u : krylov.Tensor.BinaryCubic)
    (hobs : observe r t=observe r u) :
    ‖(planeTerminalOperator r u-planeTerminalOperator r t) (planeTerminalRho r t)‖/2=
      r^2/4*chordValue r t u*Real.sqrt (1+4*r^2) := by
  rw [planeTerminal_difference_rho r t u hobs,norm_smul,Real.norm_eq_abs,planarFibreDirection_norm]
  simp only [abs_div,abs_mul,abs_of_nonneg (sq_nonneg r)]
  rw [show |(4:ℝ)|=4 by norm_num]
  unfold chordValue
  rw [abs_sub_comm u.t2 t.t2]
  ring

/-- A genuine two-scenario perturbation of a common affine gradient has its
sharp cubic half-distance coefficient and a controlled fourth-order loss.
Article: main_krylov, prop:Fcycle(iii), finite-scale algebraic radius. -/
theorem nonlinear_two_scenario_cubic_lower {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (ρ s g₀ g₁ : V) (L₀ L₁ : V →L[ℝ] V) (p A M C : ℝ)
    (hp : 0<p) (hp₁ : p≤1) (hA : 0≤A) (hM : 0≤M) (hC : 0≤C)
    (hs : ‖s‖≤M*p^2) (hg₀ : ‖g₀‖≤A*p^3)
    (he₀ : ‖g₀-(p^2 • ρ+s+p • L₀ s)‖≤C*p^4)
    (he₁ : ‖g₁-(p^2 • ρ+s+p • L₁ s)‖≤C*p^4) :
    ‖(L₁-L₀) ρ‖/2*p^3-
      (C+‖L₁-L₀‖*(A+‖L₀‖*M+C)/2)*p^4≤max ‖g₀‖ ‖g₁‖ := by
  let e₀ := g₀-(p^2 • ρ+s+p • L₀ s)
  let e₁ := g₁-(p^2 • ρ+s+p • L₁ s)
  let D := A+‖L₀‖*M+C
  have hD : 0≤D := by dsimp only [D]; positivity
  have hp₃ : 0≤p^3 := by positivity
  have hp₄ : 0≤p^4 := by positivity
  have hL₀ : ‖p • L₀ s‖≤‖L₀‖*M*p^3 := by
    rw [norm_smul,Real.norm_of_nonneg hp.le]
    exact (mul_le_mul_of_nonneg_left ((L₀.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hs (norm_nonneg _))) hp.le).trans_eq (by ring)
  have he₀' : ‖e₀‖≤C*p^3 := he₀.trans (by
    have hh := mul_le_mul_of_nonneg_left hp₁ (mul_nonneg hC hp₃)
    nlinarith only [hh])
  have hclose : ‖s+p^2 • ρ‖≤D*p^3 := by
    have he : s+p^2 • ρ=(g₀-p • L₀ s)-e₀ := by dsimp only [e₀]; abel
    rw [he]
    calc
      _ ≤ ‖g₀-p • L₀ s‖+‖e₀‖ := norm_sub_le _ _
      _ ≤ (‖g₀‖+‖p • L₀ s‖)+‖e₀‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (A*p^3+‖L₀‖*M*p^3)+C*p^3 := add_le_add (add_le_add hg₀ hL₀) he₀'
      _ = D*p^3 := by dsimp only [D]; ring
  have herror : ‖(g₁-g₀)+p^3 • (L₁-L₀) ρ‖≤(2*C+‖L₁-L₀‖*D)*p^4 := by
    have he : (g₁-g₀)+p^3 • (L₁-L₀) ρ=(e₁-e₀)+p • (L₁-L₀) (s+p^2 • ρ) := by
      simp only [e₀,e₁,map_add,map_smul,sub_apply,smul_add,smul_sub,smul_smul]
      module
    rw [he]
    have hlast : ‖p • (L₁-L₀) (s+p^2 • ρ)‖≤‖L₁-L₀‖*D*p^4 := by
      rw [norm_smul,Real.norm_of_nonneg hp.le]
      exact (mul_le_mul_of_nonneg_left (((L₁-L₀).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left hclose (norm_nonneg _))) hp.le).trans_eq (by ring)
    exact (norm_add_le _ _).trans ((add_le_add ((norm_sub_le _ _).trans (add_le_add he₁ he₀)) hlast).trans_eq (by ring))
  have hn : p^3*‖(L₁-L₀) ρ‖≤2*max ‖g₀‖ ‖g₁‖+(2*C+‖L₁-L₀‖*D)*p^4 := by
    have hh := norm_sub_le ((g₁-g₀)+p^3 • (L₁-L₀) ρ) (g₁-g₀)
    rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hp₃] at hh
    have hd := norm_sub_le g₁ g₀
    nlinarith only [hh,herror,hd,le_max_left ‖g₀‖ ‖g₁‖,le_max_right ‖g₀‖ ‖g₁‖]
  dsimp only [D] at hn
  nlinarith only [hn]

set_option maxHeartbeats 600000 in
/-- Every unrestricted common output of two exact indistinguishable scalar
cubics obeys the sharp leading binary-chord information lower bound, with a
genuine uniform fourth-order loss. Article: main_krylov, prop:Fcycle(iii).
The actual objectives and actual Euclidean Riesz gradients occur literally;
no small-output or small-correction assumption occurs in the conclusion. -/
theorem planeCubic_all_output_chord_lower (r : ℝ) (t u : krylov.Tensor.BinaryCubic)
    (hobs : observe r t=observe r u) (hd : u.t2-t.t2≠0) (hr : r≠0) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → p≤1 → ∀ x : Plane,
      r^2/4*chordValue r t u*Real.sqrt (1+4*r^2)*p^3-C*p^4≤
        max ‖gradient (planeCubicObjective p r t) x‖ ‖gradient (planeCubicObjective p r u) x‖ := by
  let L₀ := planeTerminalOperator r t
  let L₁ := planeTerminalOperator r u
  let ρ := planeTerminalRho r t
  let A := ‖(L₁-L₀) ρ‖/2+1
  have hA : 0<A := by dsimp only [A]; positivity
  obtain ⟨M,hM,hloc⟩ := planarCubic_common_output_coordinate_localization r t u hobs hd hr A hA.le
  obtain ⟨E,hE,haffine⟩ := planeCubic_common_output_affine_error r t u hobs hd hr A hA.le
  let C := E+‖L₁-L₀‖*(A+‖L₀‖*(2*M)+E)/2+1
  have hC : 0<C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro p hp hp₁ x
  let g₀ := gradient (planeCubicObjective p r t) x
  let g₁ := gradient (planeCubicObjective p r u) x
  have hinfo : ‖(L₁-L₀) ρ‖/2=r^2/4*chordValue r t u*Real.sqrt (1+4*r^2) :=
    planeTerminal_information_norm r t u hobs
  have hp₃ : 0≤p^3 := by positivity
  have hp₄ : 0≤p^4 := by positivity
  by_cases hsmall : max ‖g₀‖ ‖g₁‖≤A*p^3
  · have ht : ‖g₀‖≤A*p^3 := (le_max_left _ _).trans hsmall
    have hu : ‖g₁‖≤A*p^3 := (le_max_right _ _).trans hsmall
    have htc : ‖planarCubicGradient p r t (pairOfPlane x)‖≤A*p^3 := by
      have hb := pair_norm_le_planeOfPair (planarCubicGradient p r t (pairOfPlane x))
      exact hb.trans ((congrArg norm (planeCubicGradient_actual p r t x)).symm.le.trans ht)
    have huc : ‖planarCubicGradient p r u (pairOfPlane x)‖≤A*p^3 := by
      have hb := pair_norm_le_planeOfPair (planarCubicGradient p r u (pairOfPlane x))
      exact hb.trans ((congrArg norm (planeCubicGradient_actual p r u x)).symm.le.trans hu)
    let s := planeOfPair (pairOfPlane x-(p,r*p))
    have hs : ‖s‖≤(2*M)*p^2 :=
      (planeOfPair_norm_le _).trans ((mul_le_mul_of_nonneg_left
        (hloc p hp hp₁ (pairOfPlane x) htc huc) (by norm_num : (0:ℝ)≤2)).trans_eq (by ring))
    have he := haffine p hp hp₁ x ht hu
    have he₀ : ‖g₀-(p^2 • ρ+s+p • L₀ s)‖≤E*p^4 := by
      rw [planeTerminalModel_eq] at he
      exact he.1
    have he₁ : ‖g₁-(p^2 • ρ+s+p • L₁ s)‖≤E*p^4 := by
      have hh := he.2
      rw [planeTerminalModel_eq,←planeTerminalRho_eq r t u hobs] at hh
      exact hh
    have hb := nonlinear_two_scenario_cubic_lower ρ s g₀ g₁ L₀ L₁ p A (2*M) E
      hp hp₁ hA.le (by positivity) hE.le hs ht he₀ he₁
    rw [hinfo] at hb
    have hcoef : E+‖L₁-L₀‖*(A+‖L₀‖*(2*M)+E)/2≤C := by dsimp only [C]; linarith
    exact (sub_le_sub_left (mul_le_mul_of_nonneg_right hcoef hp₄) _).trans hb
  · have hl : ‖(L₁-L₀) ρ‖/2*p^3≤max ‖g₀‖ ‖g₁‖ :=
      (mul_le_mul_of_nonneg_right (by dsimp only [A]; linarith : ‖(L₁-L₀) ρ‖/2≤A) hp₃).trans
        (lt_of_not_ge hsmall).le
    rw [hinfo] at hl
    exact (sub_le_self _ (mul_nonneg hC.le hp₄)).trans hl

end
end krylov.Functions
