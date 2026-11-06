import nesterov.Realization.RestRate
import nesterov.Momentum.RestQuadratic
import nesterov.Momentum.QuadraticDictionary

/-! Scalar quadratic lower bounds for the literal finite-dimensional rest rate. -/
noncomputable section
open Filter Set
open scoped Topology
namespace nesterov.Momentum

/-- The literal one-dimensional quadratic belongs to the article's centered
smooth strongly convex class, including the endpoint curvatures. -/
theorem real_quadratic_centered {μ L lam : ℝ} (hμ : 0<μ) (hμL : μ<L)
    (hlam : lam∈Icc μ L) :
    polyak.CenteredSmoothStronglyConvex μ L (fun x : ℝ=>lam/2*‖x‖^2) := by
  let c := Rates.normalizedCurvature μ L lam
  have hc : |c|≤1 := Rates.abs_normalizedCurvature_le_one hμL hlam
  have hg (x : ℝ) : HasGradientAt (fun x : ℝ=>c/2*‖x‖^2) (c • x) x := by
    simpa using polyak.hasGradientAt_quadratic_add (hasGradientAt_const x (0:ℝ)) c 0
  have hn : polyak.NormalizedSmooth (fun x : ℝ=>c/2*‖x‖^2) := by
    refine ⟨fun x=>(hg x).differentiableAt,?_,by simp,?_⟩
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [dist_eq_norm,(hg x).gradient,(hg y).gradient,NNReal.coe_one,one_mul]
      rw [←smul_sub,norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (one_mul _)
    · rw [(hg 0).gradient,smul_zero]
  have he : polyak.denormalizeFunction μ L (fun x : ℝ=>c/2*‖x‖^2)=
      (fun x : ℝ=>lam/2*‖x‖^2) := by
    funext x
    dsimp [polyak.denormalizeFunction,c,Rates.normalizedCurvature]
    field_simp [ne_of_gt (sub_pos.mpr hμL)]
    ring
  rw [←he]
  exact hn.denormalize hμ hμL

theorem real_quadratic_gradient (lam x : ℝ) :
    gradient (fun x : ℝ=>lam/2*‖x‖^2) x=lam*x := by
  have hg : HasGradientAt (fun x : ℝ=>lam/2*‖x‖^2) (lam • x) x := by
    simpa using polyak.hasGradientAt_quadratic_add (hasGradientAt_const x (0:ℝ)) lam 0
  exact hg.gradient

/-- Every scalar quadratic root radius is seen by the literal from-rest rate. -/
theorem scalarRadius_le_momentumRestRate {μ L β τ h lam : ℝ}
    (hh : 0<h) (hμ : 0<μ) (hμL : μ<L) (hlam : lam∈Icc μ L) :
    Quadratic.scalarRadius β τ h lam≤momentumRestRate β τ h hh.ne' μ L := by
  have h := iterate_root_limsup_le_restRate (β:=β) (τ:=τ) hh.ne'
    (real_quadratic_centered hμ hμL hlam) (x₀:=1) one_ne_zero
  have hg : gradient (fun x : ℝ=>lam/2*‖x‖^2)=(fun x : ℝ=>lam*x) :=
    funext (real_quadratic_gradient lam)
  rw [hg] at h
  simpa only [Real.norm_eq_abs,quadratic_iterate_root_limsup hh (hμ.trans_le hlam.1) one_ne_zero] using h

/-- The actual scalar-quadratic maximum is a lower bound for the source
from-rest rate, without the common-factor exclusion used for queries. -/
theorem quadraticRate_le_momentumRestRate {μ L β τ h : ℝ}
    (hh : 0<h) (hμ : 0<μ) (hμL : μ<L) :
    Quadratic.quadraticRate μ L β τ h≤momentumRestRate β τ h hh.ne' μ L := by
  apply csSup_le (Quadratic.rootNorms_nonempty hμL.le β τ h)
  rintro r ⟨lam,hlam,z,hz,rfl⟩
  exact ((Quadratic.scalarRadius_isGreatest β τ h lam).2 ⟨z,hz,rfl⟩).trans
    (scalarRadius_le_momentumRestRate hh hμ hμL hlam)

/-- A maximizing curvature gives one fixed genuine scalar quadratic and one
fixed nonzero start attaining the entire quadratic worst-case factor. -/
theorem exists_real_quadratic_rest_attainment {μ L β τ h : ℝ}
    (hh : 0<h) (hμ : 0<μ) (hμL : μ<L) :
    ∃ lam∈Icc μ L,polyak.CenteredSmoothStronglyConvex μ L (fun x : ℝ=>lam/2*‖x‖^2) ∧
      limsup (fun n : ℕ=>‖iterate (gradient (fun x : ℝ=>lam/2*‖x‖^2)) β τ h 1 n‖^
        ((n:ℝ)⁻¹)) atTop=Quadratic.quadraticRate μ L β τ h := by
  obtain ⟨lam,hlam,z,hz,he⟩ := (Quadratic.quadraticRate_isGreatest_general hμL.le).1
  have hrad : Quadratic.scalarRadius β τ h lam=Quadratic.quadraticRate μ L β τ h := by
    apply le_antisymm
    · obtain ⟨z',hz',hr⟩ := (Quadratic.scalarRadius_isGreatest β τ h lam).1
      rw [hr]
      exact Quadratic.root_norm_le_rate_general hμL.le hlam hz'
    · rw [he]
      exact (Quadratic.scalarRadius_isGreatest β τ h lam).2 ⟨z,hz,rfl⟩
  refine ⟨lam,hlam,real_quadratic_centered hμ hμL hlam,?_⟩
  have hg : gradient (fun x : ℝ=>lam/2*‖x‖^2)=(fun x : ℝ=>lam*x) :=
    funext (real_quadratic_gradient lam)
  rw [hg]
  simpa only [Real.norm_eq_abs,hrad] using
    quadratic_iterate_root_limsup (β:=β) (τ:=τ) hh (hμ.trans_le hlam.1) (x₀:=1) one_ne_zero
end nesterov.Momentum
