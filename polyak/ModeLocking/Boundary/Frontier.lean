import polyak.ModeLocking.Boundary.Definitions

/-! Every zero of the actual threshold is on the divergence boundary. -/
noncomputable section
namespace polyak.ModeLocking
open General Levels Set Filter
open scoped Topology

def lowerKappa (q:Tuning) (j:ℕ) : Tuning where
  kappa:=q.kappa-(q.kappa-1)/((j:ℝ)+2)
  y:=q.y
  beta:=q.beta
  kappa_gt_one:=by
    have hh:(q.kappa-1)/((j:ℝ)+2)<q.kappa-1:=
      (div_lt_iff₀ (by positivity : (0:ℝ)<(j:ℝ)+2)).mpr
        (by nlinarith [q.kappa_gt_one])
    linarith
  beta_nonneg:=q.beta_nonneg
  beta_lt_one:=q.beta_lt_one
  y_pos:=q.y_pos
  y_lt:=q.y_lt

theorem lowerKappa_lt (q:Tuning) (j:ℕ) : (lowerKappa q j).kappa<q.kappa := by
  change q.kappa-(q.kappa-1)/((j:ℝ)+2)<q.kappa
  have hp:0<(q.kappa-1)/((j:ℝ)+2):=div_pos (sub_pos.mpr q.kappa_gt_one) (by positivity)
  linarith

theorem lowerKappa_tendsto (q:Tuning) : Tendsto (lowerKappa q) atTop (𝓝 q) := by
  rw [show (𝓝 q)=Filter.comap (fun p:Tuning=>(p.kappa,p.y,p.beta))
    (𝓝 (q.kappa,q.y,q.beta)) from nhds_induced _ _]
  apply tendsto_comap_iff.mpr
  have ht:Tendsto (fun j:ℕ=>((j:ℝ)+2)) atTop atTop:=tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have he:Tendsto (fun j:ℕ=>(q.kappa-1)/((j:ℝ)+2)) atTop (𝓝 0):=
    tendsto_const_nhds.div_atTop ht
  have hκ:Tendsto (fun j:ℕ=>q.kappa-(q.kappa-1)/((j:ℝ)+2)) atTop (𝓝 q.kappa):=by
    simpa only [sub_zero] using (tendsto_const_nhds (x:=q.kappa)).sub he
  exact hκ.prodMk_nhds (tendsto_const_nhds.prodMk_nhds tendsto_const_nhds)

theorem mem_frontier_iff_sigma_zero (q:Tuning) :
    q∈frontier Regions.divergenceSet ↔ Threshold.sigma q=0 := by
  constructor
  · exact Global.Threshold.sigma_eq_zero_on_frontier
  · intro hq
    rw [frontier_eq_closure_inter_closure]
    constructor
    · exact subset_closure ((divergenceSet_iff_sigma_nonpos q).mpr hq.le)
    · apply mem_closure_of_tendsto (lowerKappa_tendsto q)
      apply Eventually.of_forall
      intro j
      have hp:=Global.Threshold.sigma_strictAnti_kappa (lowerKappa q j) q rfl rfl (lowerKappa_lt q j)
      change lowerKappa q j∉Regions.divergenceSet
      rw [divergenceSet_iff_sigma_nonpos]
      change Threshold.sigma q<Threshold.sigma (lowerKappa q j) at hp
      rw [hq] at hp
      exact not_le_of_gt hp

theorem boundaryInGap_iff (K:ℕ) (q:Tuning) :
    q∈BoundaryInGap K ↔ Geometry.Gap K q ∧ Threshold.sigma q=0 := by
  change (_ ∧ _)↔_
  rw [mem_frontier_iff_sigma_zero]
  exact and_comm

theorem boundaryInGap_relatively_closed (K:ℕ) :
    IsClosed {q:{q:Tuning//Geometry.Gap K q}|q.val∈BoundaryInGap K} := by
  have hc:IsClosed {q:Tuning|Threshold.sigma q=0}:=
    isClosed_eq Global.Threshold.continuous_sigma continuous_const
  convert hc.preimage continuous_subtype_val using 1
  ext q
  change (q.val∈BoundaryInGap K)↔Threshold.sigma q.val=0
  rw [boundaryInGap_iff]
  exact ⟨And.right,fun h=>⟨q.property,h⟩⟩

end polyak.ModeLocking
