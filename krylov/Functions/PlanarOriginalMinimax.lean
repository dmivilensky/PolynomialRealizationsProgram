import krylov.Functions.PlanarBetaMinimax
import krylov.Functions.PlanarRFCFUnknownBase

/-!
Article: main_krylov, thm:Fplanar, original unknown-base planar minimax.
Use: take the actual infimum of full source suprema with the ORIGINAL
independent first-secant diagonal beta, rather than a tensor-dependent
centered parameter. The genuine information chord belongs to this original
interval by the sharp mixed-tensor bound. The real endpoint-only centre
attains the same leading constant for all independent original bases.
Source: true scalar derivatives, exact source reparameterization and the
proved binary all-policy lower and observed-centre upper bounds.
-/
namespace krylov.Functions
noncomputable section
open krylov.Tensor.BinaryCubic
open scoped ENNReal

/-- The sharp bound needed to place a value-information fibre inside the
original unknown-base interval. Article: main_krylov, prop:Fcycle(iii). -/
theorem binary_last_base_bound (r : ℝ) (t : krylov.Tensor.BinaryCubic) (ht : t.InBall) :
    |t.t2+r*t.t3|≤Real.sqrt (1+r^2) := by
  let u : krylov.Tensor.BinaryCubic := ⟨t.t3,t.t2,t.t1,t.t0⟩
  have hu : u.InBall := by
    intro c s hcs
    have he : u.eval c s=t.eval s c := by dsimp only [u,eval]; ring
    rw [he]
    exact ht s c (by linarith only [hcs])
  have hd : t.t2^2+t.t3^2≤1 := by
    have hh := (coefficient_disks hu).1
    change t.t3^2+t.t2^2≤1 at hh
    linarith only [hh]
  have hsq := Real.sq_sqrt (by positivity : 0≤1+r^2)
  have hdot : (t.t2+r*t.t3)^2≤1+r^2 := by
    have hh := mul_le_mul_of_nonneg_left hd (by positivity : 0≤1+r^2)
    nlinarith only [hh,sq_nonneg (r*t.t2-t.t3)]
  nlinarith only [hdot,hsq,sq_abs (t.t2+r*t.t3),abs_nonneg (t.t2+r*t.t3),Real.sqrt_nonneg (1+r^2)]

/-- The complete planar source supremum, with the original independently
unknown first-secant h-diagonal. Article: main_krylov, thm:Fplanar. -/
def planeOriginalPolicyWorst (B r p L : ℝ) (policy : Observation → Plane) : ℝ≥0∞ :=
  ⨆ t : {t : krylov.Tensor.BinaryCubic // t.InBall},
    ⨆ β : {β : ℝ // |β|≤L*p},
      ENNReal.ofReal ‖gradient (planeUnknownBaseObjective p r β.val (scaleBinaryCubic B t.val))
        (policy (observe r (scaleBinaryCubic B t.val)))‖

/-- The literal original-base infimum of actual scalar source suprema.
Every unrestricted observation-only output is allowed. Article: thm:Fplanar. -/
def planeOriginalPolicyMinimax (B r p L : ℝ) : ℝ≥0∞ :=
  ⨅ policy : Observation → Plane, planeOriginalPolicyWorst B r p L policy

/-- The centered zero-beta information family is contained in the full
original source class whenever its sharp radius fits that class.
Article: main_krylov, thm:Fplanar, admissibility of the lower witnesses. -/
theorem planeOriginalPolicyWorst_contains_fibre (B r p L : ℝ) (hB : 0<B) (hp : 0<p)
    (hL : B/2*Real.sqrt (1+r^2)≤L) (policy : Observation → Plane) :
    planeBetaPolicyWorst B r p 0 policy≤planeOriginalPolicyWorst B r p L policy := by
  apply iSup_le
  intro t
  apply iSup_le
  intro β
  have hz : β.val=0 := by
    have hb := β.property
    simp only [zero_mul] at hb
    exact abs_nonpos_iff.mp hb
  let q := scaleBinaryCubic B t.val
  let b := -(p*(q.t2+r*q.t3)/2)
  have hq : |q.t2+r*q.t3|≤B*Real.sqrt (1+r^2) := by
    have he : q.t2+r*q.t3=B*(t.val.t2+r*t.val.t3) := by dsimp only [q,scaleBinaryCubic]; ring
    rw [he,abs_mul,abs_of_pos hB]
    exact mul_le_mul_of_nonneg_left (binary_last_base_bound r t.val t.property) hB.le
  have hb : |b|≤L*p := by
    dsimp only [b]
    rw [abs_neg,abs_div,abs_mul,abs_of_pos hp,show |(2:ℝ)|=2 by norm_num]
    have hh := mul_le_mul_of_nonneg_left hq hp.le
    have hl := mul_le_mul_of_nonneg_right hL hp.le
    nlinarith only [hh,hl]
  apply le_iSup_of_le t
  apply le_iSup_of_le ⟨b,hb⟩
  have he : b+p*(q.t2+r*q.t3)/2=0 := neg_add_cancel _
  change ENNReal.ofReal ‖gradient (planeBetaCubicObjective p r β.val q) (policy (observe r q))‖≤
    ENNReal.ofReal ‖gradient (planeBetaCubicObjective p r (b+p*(q.t2+r*q.t3)/2) q) (policy (observe r q))‖
  rw [hz,he]

/-- Every original independent-base source is in a common centered-beta
tube; the tube enlargement changes only the fourth-order remainder.
Article: main_krylov, thm:Fplanar. -/
theorem planeOriginalPolicyWorst_le_beta (B r p L : ℝ) (hB : 0<B) (hp : 0<p)
    (policy : Observation → Plane) :
    planeOriginalPolicyWorst B r p L policy≤
      planeBetaPolicyWorst B r p (L+B/2*Real.sqrt (1+r^2)) policy := by
  apply iSup_le
  intro t
  apply iSup_le
  intro β
  let q := scaleBinaryCubic B t.val
  let b := β.val+p*(q.t2+r*q.t3)/2
  have hq : |q.t2+r*q.t3|≤B*Real.sqrt (1+r^2) := by
    have he : q.t2+r*q.t3=B*(t.val.t2+r*t.val.t3) := by dsimp only [q,scaleBinaryCubic]; ring
    rw [he,abs_mul,abs_of_pos hB]
    exact mul_le_mul_of_nonneg_left (binary_last_base_bound r t.val t.property) hB.le
  have hb : |b|≤(L+B/2*Real.sqrt (1+r^2))*p := by
    apply (abs_add_le _ _).trans
    rw [abs_div,abs_mul,abs_of_pos hp,show |(2:ℝ)|=2 by norm_num]
    have hh := mul_le_mul_of_nonneg_left hq hp.le
    nlinarith only [β.property,hh]
  exact le_iSup_of_le t (le_iSup_of_le ⟨b,hb⟩ le_rfl)

/-- The complete independent-original-base minimax has its printed sharp
cubic coefficient and one uniform fourth-order loss on both sides.
The actual endpoint-only known-budget centre realizes the upper bound.
Article: main_krylov, thm:Fplanar, original beta and full tensor budget. -/
theorem planeOriginalPolicyMinimax_bounds (B r L : ℝ) (hB : 0<B) (hr : 0<r)
    (hL : B/2*Real.sqrt (1+r^2)≤L) :
    ∃ C : ℝ, 0<C ∧ ∀ p : ℝ, 0<p → B*p≤1 →
      ENNReal.ofReal (B^2*(r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r)*p^3-C*p^4)≤
        planeOriginalPolicyMinimax B r p L ∧
      planeOriginalPolicyMinimax B r p L≤
        planeOriginalPolicyWorst B r p L (budgetedPlaneCentreOutput B r p) ∧
      planeOriginalPolicyWorst B r p L (budgetedPlaneCentreOutput B r p)≤
        ENNReal.ofReal (B^2*(r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r)*p^3+C*p^4) := by
  have hL₀ : 0≤L := (mul_nonneg (div_nonneg hB.le (by norm_num)) (Real.sqrt_nonneg _)).trans hL
  obtain ⟨Cl,hCl,hlower⟩ := planeBetaPolicyWorst_lower B r hB hr
  obtain ⟨Cu,hCu,hupper⟩ := planeBetaPolicyWorst_centre_upper B r (L+B/2*Real.sqrt (1+r^2)) hB
    (by positivity)
  refine ⟨Cl+Cu,by positivity,?_⟩
  intro p hp hp₁
  refine ⟨?_,iInf_le _ _,?_⟩
  · apply le_iInf
    intro policy
    apply (ENNReal.ofReal_le_ofReal (sub_le_sub_left
      (mul_le_mul_of_nonneg_right (by linarith only [hCu] : Cl≤Cl+Cu) (pow_nonneg hp.le 4)) _)).trans
    exact (hlower p 0 hp hp₁ le_rfl policy).trans
      (planeOriginalPolicyWorst_contains_fibre B r p L hB hp hL policy)
  · apply (planeOriginalPolicyWorst_le_beta B r p L hB hp _).trans
    exact (hupper p hp hp₁).trans (ENNReal.ofReal_le_ofReal (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (by linarith only [hCl] : Cu≤Cl+Cu) (pow_nonneg hp.le 4))))

end
end krylov.Functions
