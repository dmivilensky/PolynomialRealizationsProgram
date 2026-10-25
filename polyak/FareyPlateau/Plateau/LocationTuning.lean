import polyak.FareyPlateau.Plateau.LocationBeta

/-! The remaining coordinates in Proposition location: the actual tuning,
including the condition number, has the asserted boundary limit. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels Filter Set Topology

theorem tuningA_edge (q : Tuning) {c h a D : ℝ} (ha : a≠0)
    (he : Chart.coefficients q=edgeCoefficients c h a D) :
    q.A=2*q.beta*(2*c+(1+D)/a)/(1+q.beta) := by
  have h1 := congrArg Chart.Coefficients.c1 he
  have h2 := congrArg Chart.Coefficients.c2 he
  dsimp [Chart.coefficients,edgeCoefficients] at h1 h2
  have hd : 2*q.B*(1-q.beta)≠0 := by positivity [q.B_pos,q.beta_lt_one]
  rw [div_eq_iff hd] at h1 h2
  have hp : 1+q.beta≠0 := by linarith [q.beta_nonneg]
  field_simp [ha,hp]
  linear_combination (a/2)*h1 + ((1+D+2*a*c)/2)*h2

theorem inverseB_edge (C : Chart.CoefficientPoint) {c h a D : ℝ}
    (he : C.val=edgeCoefficients c h a D) :
    Chart.inverseB C=(1-Chart.inverseBeta C)/shiftedEdgeRoot C a := by
  simp only [Chart.inverseB,edgeRoot_normalizedB C he,div_eq_mul_inv,one_mul]

theorem location_tuning {ι : Type*} {l : Filter ι}
    (C : ι→Chart.CoefficientPoint) (a : ι→ℝ) {c h D : ℝ}
    (he : ∀i,(C i).val=edgeCoefficients c h (a i) D)
    (hc : c∈Ioo (-1:ℝ) 1) (hh : 0<h) (ha : Tendsto a l atTop) :
    Tendsto (fun i=>(Chart.inverseTuning (C i)).beta) l (𝓝 1) ∧
    Tendsto (fun i=>a i*(1-(Chart.inverseTuning (C i)).beta)^2)
      l (𝓝 (2*edgeRootLimit c h)) ∧
    Tendsto (fun i=>(Chart.inverseTuning (C i)).y) l (𝓝 (2-2*c)) ∧
    Tendsto (fun i=>(Chart.inverseTuning (C i)).kappa) l (𝓝 1) := by
  have hβ := inverseBeta_edge_tendsto C a he hc hh ha
  have hr := shiftedEdgeRoot_tendsto C a he hc hh ha
  have hB : Tendsto (fun i=>Chart.inverseB (C i)) l (𝓝 0) := by
    have ht := ((tendsto_const_nhds (x:=(1:ℝ))).sub hβ).div hr (edgeRootLimit_pos hh).ne'
    change Tendsto (fun i=>(1-Chart.inverseBeta (C i))/shiftedEdgeRoot (C i) (a i))
      l (𝓝 ((1-1)/edgeRootLimit c h)) at ht
    simpa only [sub_self,zero_div,←inverseB_edge _ (he _)] using ht
  have ha0 := ha.const_div_atTop (1+D)
  have hA : Tendsto (fun i=>Chart.inverseA (C i)) l (𝓝 (2*c)) := by
    have hrep (i) : Chart.inverseA (C i)=
        2*Chart.inverseBeta (C i)*(2*c+(1+D)/a i)/(1+Chart.inverseBeta (C i)) := by
      have hap := (C i).property.1
      rw [he i] at hap
      change -(a i)<0 at hap
      have ht := tuningA_edge (Chart.inverseTuning (C i)) (by linarith : a i≠0)
        ((Chart.coefficients_inverseTuning (C i)).trans (he i))
      simpa only [Chart.inverseTuning_A,Chart.inverseTuning_beta] using ht
    have ht := ((hβ.const_mul 2).mul ((tendsto_const_nhds (x:=2*c)).add ha0)).div
      ((tendsto_const_nhds (x:=(1:ℝ))).add hβ) (by norm_num : (1:ℝ)+1≠0)
    convert ht using 1
    · funext i; exact hrep i
    · congr 1; ring
  have hy : Tendsto (fun i=>(Chart.inverseTuning (C i)).y) l (𝓝 (2-2*c)) := by
    have ht := (((tendsto_const_nhds (x:=(1:ℝ))).add hβ).sub hA).add hB
    simpa only [Chart.inverseTuning_y,Chart.inverseY,add_zero,one_add_one_eq_two] using ht
  have hx : Tendsto (fun i=>(Chart.inverseTuning (C i)).x) l (𝓝 (2-2*c)) := by
    have ht := (((tendsto_const_nhds (x:=(1:ℝ))).add hβ).sub hA).sub hB
    simpa only [Chart.inverseTuning_x,Chart.inverseX,sub_zero,one_add_one_eq_two] using ht
  have hκ : Tendsto (fun i=>(Chart.inverseTuning (C i)).kappa) l (𝓝 1) := by
    have hden : 2-2*c≠0 := by linarith [hc.2]
    have ht := hy.div hx hden
    have hrep (i) : (Chart.inverseTuning (C i)).y/(Chart.inverseTuning (C i)).x=
        (Chart.inverseTuning (C i)).kappa := by
      unfold Tuning.x
      field_simp
      rw [mul_div_cancel_left₀ _ (Chart.inverseTuning (C i)).y_pos.ne']
    change Tendsto (fun i=>(Chart.inverseTuning (C i)).y /
      (Chart.inverseTuning (C i)).x) l (𝓝 ((2-2*c)/(2-2*c))) at ht
    simpa only [hrep,div_self hden] using ht
  exact ⟨hβ,scale_edge_tendsto C a he hc hh ha,hy,hκ⟩

end polyak.FareyPlateau
