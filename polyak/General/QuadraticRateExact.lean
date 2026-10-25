import polyak.General.QuadraticRateBounds
import polyak.General.QuadraticScalarLower

/-! The characteristic-root factor is exactly the actual quadratic-class
rate from rest. A single genuine scalar quadratic supplies each lower
asymptotic bound; the upper estimate is uniform over all finite-dimensional
shifted quadratics. -/
noncomputable section
namespace polyak.General
open Filter Set
open scoped Topology

def scalarQuadraticModel (μ L lam : ℝ) (hlam : lam∈Icc μ L) : QuadraticModel μ L 1 where
  H:=lam • LinearMap.id
  symmetric:=by
    intro x y
    simp only [LinearMap.smul_apply,LinearMap.id_apply,inner_smul_left,inner_smul_right,
      starRingEnd_apply,star_trivial]
  lower:=by
    intro v
    simpa only [LinearMap.smul_apply,LinearMap.id_apply,inner_smul_left,
      starRingEnd_apply,star_trivial,real_inner_self_eq_norm_sq] using
      mul_le_mul_of_nonneg_right hlam.1 (sq_nonneg ‖v‖)
  upper:=by
    intro v
    simpa only [LinearMap.smul_apply,LinearMap.id_apply,inner_smul_left,
      starRingEnd_apply,star_trivial,real_inner_self_eq_norm_sq] using
      mul_le_mul_of_nonneg_right hlam.2 (sq_nonneg ‖v‖)
  center:=0
  constant:=0

def scalarQuadraticStart : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1

@[simp] theorem scalarQuadraticStart_norm : ‖scalarQuadraticStart‖=1 := by
  simp [scalarQuadraticStart,PiLp.norm_single]

theorem scalarQuadraticModel_iterate (μ L α β lam : ℝ) (hlam : lam∈Icc μ L) (n : ℕ) :
    Dynamics.iterate (gradient (scalarQuadraticModel μ L lam hlam).potential) α β
      scalarQuadraticStart n=
      quadraticScalar (1+β-α*lam) β n • scalarQuadraticStart := by
  have hg : gradient (scalarQuadraticModel μ L lam hlam).potential=
      (fun x : EuclideanSpace ℝ (Fin 1)=>lam • x) := by
    funext x
    rw [QuadraticModel.gradient_potential]
    simp only [scalarQuadraticModel,sub_zero,LinearMap.smul_apply,LinearMap.id_apply]
  rw [hg,QuadraticDiagonal.isotropic_iterate,quadraticScalar_iterate]

/-- This lower witness is one fixed actual quadratic and one fixed start
before all horizons, with the source's prescribed zero momentum. -/
theorem quadraticScalar_abs_mem_quadraticRatios (μ L α β lam : ℝ)
    (hlam : lam∈Icc μ L) (n : ℕ) :
    |quadraticScalar (1+β-α*lam) β n|∈quadraticRatios μ L α β n := by
  refine ⟨1,by norm_num,scalarQuadraticModel μ L lam hlam,scalarQuadraticStart,?_,?_⟩
  · intro hh
    have hn:=scalarQuadraticStart_norm
    change scalarQuadraticStart=0 at hh
    rw [hh,norm_zero] at hn
    norm_num at hn
  · rw [scalarQuadraticModel_iterate]
    simp only [scalarQuadraticModel,sub_zero,norm_smul,Real.norm_eq_abs,
      scalarQuadraticStart_norm,mul_one,div_one]

theorem quadraticScalar_abs_le_quadraticWorst {μ L α β lam : ℝ}
    (hμ : 0<μ) (hL : μ<L) (hα : 0≤α) (hβ : 0≤β)
    (hlam : lam∈Icc μ L) (n : ℕ) :
    |quadraticScalar (1+β-α*lam) β n|≤quadraticWorst μ L α β n :=
  le_csSup (quadraticRatios_bddAbove hμ hL hα hβ n)
    (mem_insert_of_mem _ (quadraticScalar_abs_mem_quadraticRatios μ L α β lam hlam n))

theorem quadraticScalarRate_le_quadraticExecutionRate {μ L α β lam : ℝ}
    (hμ : 0<μ) (hL : μ<L) (hα : 0≤α) (hβ : 0≤β) (hlam : lam∈Icc μ L) :
    quadraticScalarRate (1+β-α*lam) β≤quadraticExecutionRate μ L α β := by
  have hu (n : ℕ) : |quadraticScalar (1+β-α*lam) β n|^((n:ℝ)⁻¹)≤
      quadraticWorst μ L α β n^((n:ℝ)⁻¹) :=
    Real.rpow_le_rpow (abs_nonneg _)
      (quadraticScalar_abs_le_quadraticWorst hμ hL hα hβ hlam n) (by positivity)
  have hb : IsBoundedUnder (·≤·) atTop
      (fun n : ℕ=>quadraticWorst μ L α β n^((n:ℝ)⁻¹)) := by
    apply isBoundedUnder_of
    refine ⟨1+α*L+2*β,fun n=>?_⟩
    exact (Real.rpow_le_rpow (quadraticWorst_nonneg hμ hL hα hβ n)
      (quadraticWorst_le_worstAll hμ hL hα hβ n) (by positivity)).trans
        (Dynamics.worstAll_root_le hμ hL hα hβ n)
  exact limsup_le_limsup (Eventually.of_forall hu)
    (isCoboundedUnder_le_of_le atTop (fun n=>Real.rpow_nonneg (abs_nonneg _) _)) hb

theorem rootRadius_curvature_le_quadraticExecutionRate {μ L α β lam : ℝ}
    (hμ : 0<μ) (hL : μ<L) (hα : 0<α) (hβ : 0≤β) (hlam : lam∈Icc μ L) :
    rootRadius (1+β-α*lam) β≤quadraticExecutionRate μ L α β := by
  have hh:=quadraticScalarRate_le_quadraticExecutionRate hμ hL hα.le hβ hlam
  have hc : 0<1+β-(1+β-α*lam) := by nlinarith [mul_pos hα (hμ.trans_le hlam.1)]
  rwa [quadraticScalarRate_eq_rootRadius hβ hc] at hh

/-- Equality with the source root maximum for the actual dimension-uniform
class of genuine quadratic objectives and its from-rest gradient executor. -/
theorem quadraticExecutionRate_eq_quadraticRate {μ L α β : ℝ}
    (hμ : 0<μ) (hL : μ<L) (hα : 0<α) (hβ : 0≤β) (hβ1 : β<1)
    (hquad : α*L<2*(1+β)) :
    quadraticExecutionRate μ L α β=Dynamics.quadraticRate μ L α β := by
  apply le_antisymm (quadraticExecutionRate_le_quadraticRate hμ hL hα hβ hβ1 hquad)
  obtain ⟨lam,hlam,z,hz,he⟩ := (Dynamics.quadraticRate_isGreatest hμ hL hα hβ hβ1 hquad).1
  have hroot:=root_norm_le hβ hz
  rw [← he] at hroot
  exact hroot.trans (rootRadius_curvature_le_quadraticExecutionRate hμ hL hα hβ hlam)

/-- The quadratic spectral factor is a direct subclass lower bound on the
original nonlinear rate. -/
theorem quadraticRate_le_originalRate_direct {μ L α β : ℝ}
    (hμ : 0<μ) (hL : μ<L) (hα : 0<α) (hβ : 0≤β) (hβ1 : β<1)
    (hquad : α*L<2*(1+β)) : Dynamics.quadraticRate μ L α β≤Dynamics.rate μ L α β := by
  rw [← quadraticExecutionRate_eq_quadraticRate hμ hL hα hβ hβ1 hquad]
  exact quadraticExecutionRate_le_rate hμ hL hα.le hβ

namespace Tuning

theorem quadraticExecutionRate_eq_rhoQ (q : Tuning) :
    General.quadraticExecutionRate q.x q.y 1 q.beta=q.rhoQ := by
  rw [General.quadraticExecutionRate_eq_quadraticRate q.x_pos q.x_lt_y
    (by norm_num : (0:ℝ)<1) q.beta_nonneg q.beta_lt_one (by simpa using q.y_lt),
    quadraticRate_eq]

theorem rhoQ_le_rate_direct (q : Tuning) : q.rhoQ≤q.rate := by
  rw [← q.quadraticExecutionRate_eq_rhoQ]
  exact quadraticExecutionRate_le_rate q.x_pos q.x_lt_y (by norm_num) q.beta_nonneg

end Tuning
end polyak.General
