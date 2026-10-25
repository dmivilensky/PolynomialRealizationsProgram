import polyak.Levels.Threshold.Kappa
import polyak.Levels.Chart.AngleGap
import polyak.General.Regions.PhaseLocking
import Mathlib.Analysis.SpecificLimits.Basic

/-! Every weak lag-one contact is an actual relative boundary point. -/
noncomputable section
namespace polyak.Levels.Geometry
open General Set Filter
open scoped Topology

def lowerKappaValue (q : Tuning) (n : ℕ) : ℝ :=
  q.kappa-(q.kappa-1)/2*(1/((n:ℝ)+1))

theorem lowerKappaValue_bounds (q : Tuning) (n : ℕ) :
    1<lowerKappaValue q n ∧ lowerKappaValue q n<q.kappa := by
  have hp : 0<(1/((n:ℝ)+1):ℝ):=by positivity
  have hu : (1/((n:ℝ)+1):ℝ)≤1:=by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
    simp
  have hq:=q.kappa_gt_one
  dsimp [lowerKappaValue]
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left hu (by linarith : 0≤(q.kappa-1)/2)]

def lowerKappaTuning (q : Tuning) (n : ℕ) : Tuning where
  kappa:=lowerKappaValue q n
  kappa_gt_one:=(lowerKappaValue_bounds q n).1
  y:=q.y
  beta:=q.beta
  beta_nonneg:=q.beta_nonneg
  beta_lt_one:=q.beta_lt_one
  y_pos:=q.y_pos
  y_lt:=q.y_lt

theorem lowerKappaTuning_tendsto (q : Tuning) :
    Tendsto (lowerKappaTuning q) atTop (𝓝 q) := by
  have hk : Tendsto (fun n:ℕ=>lowerKappaValue q n) atTop (𝓝 q.kappa):=by
    have hh:=(tendsto_const_nhds (x:=q.kappa)).sub
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul ((q.kappa-1)/2))
    simpa only [mul_zero,sub_zero,lowerKappaValue] using hh
  change Tendsto (lowerKappaTuning q) atTop
    (@nhds Tuning (TopologicalSpace.induced (fun p:Tuning=>(p.kappa,p.y,p.beta)) inferInstance) q)
  rw [nhds_induced,tendsto_comap_iff]
  exact hk.prodMk_nhds (tendsto_const_nhds.prodMk_nhds tendsto_const_nhds)

theorem weak_phase_mem_closure (q : Tuning)
    (hq : ∀ω∈Ioc (0:ℝ) Real.pi,ω/2≤q.angle ω) :
    q∈closure {p:Tuning | Regions.OmegaOne p} := by
  apply mem_closure_of_tendsto (lowerKappaTuning_tendsto q)
  apply Eventually.of_forall
  intro n
  apply (Regions.omegaOne_iff_angle _).mpr
  intro ω hω
  by_cases hp : ω=Real.pi
  · rw [hp,(lowerKappaTuning q n).angle_pi]
    linarith [Real.pi_pos]
  · have hi : ω∈Ioo (0:ℝ) Real.pi:=⟨hω.1,lt_of_le_of_ne hω.2 hp⟩
    have hXi:=Xi_strictMono_kappa (lowerKappaTuning q n) q rfl rfl
      (lowerKappaValue_bounds q n).2 ⟨Real.neg_one_le_cos ω,Real.cos_le_one ω⟩
    have hweak : q.Xi (Real.cos ω)≤1+Real.cos ω:=by
      by_contra hn
      have hh:=(Chart.angle_lt_half_iff_Xi q hi).mpr (lt_of_not_ge hn)
      exact (not_lt_of_ge (hq ω hω)) hh
    exact (Chart.angle_gt_half_iff_Xi _ hω).mpr (hXi.trans_le hweak)

theorem weak_contact_mem_frontier (q : Tuning)
    (hq : ∀ω∈Ioc (0:ℝ) Real.pi,ω/2≤q.angle ω)
    {ω : ℝ} (hω : ω∈Ioc (0:ℝ) Real.pi) (he : q.angle ω=ω/2) :
    q∈frontier {p:Tuning | Regions.OmegaOne p} := by
  rw [Regions.isOpen_omegaOne.frontier_eq]
  refine ⟨weak_phase_mem_closure q hq,?_⟩
  intro hΩ
  have hh:=(Regions.omegaOne_iff_angle q).mp hΩ ω hω
  rw [he] at hh
  exact lt_irrefl _ hh

end polyak.Levels.Geometry
