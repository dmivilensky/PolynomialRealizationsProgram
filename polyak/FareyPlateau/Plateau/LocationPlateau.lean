import polyak.FareyPlateau.Plateau.SingletonResults
import polyak.FareyPlateau.Plateau.LocationSource
import Mathlib.Topology.ClusterPt

/-! The source location limits yield the actual accumulation point of the
entire plateau projection, with an explicit sequence on one vertical ray. -/
noncomputable section
namespace polyak.FareyPlateau
open General Levels ModeLocking Plateaus Set Filter
open scoped Topology

theorem singletonPlateau_projection_accumulates {K j k : ℕ} (hK : 2≤K)
    (hf : Chart.FractionInWindow K j k) (b : ℤ) (hb0 : 0<b) (hbk : b<k)
    (hb : b*(j:ℤ)≡1 [ZMOD (k:ℤ)]) :
    AccPt (4*(Real.sin (Real.pi*j/k))^2,1)
      (𝓟 ((fun q : BoundaryTuning=>(q.val.y,q.val.beta)) ''
        singletonPlateau hK hf b hb0 hbk hb)) := by
  let a : ℕ→ℝ := fun n=>(n:ℝ)+(singletonRoof K j k b 0+1)
  have hp (n : ℕ) : singletonRoof K j k b 0<a n := by
    have hn : (0:ℝ)≤n := Nat.cast_nonneg n
    dsimp [a]
    linarith
  let p : ℕ→upperRoof (singletonRoof K j k b) := fun n=>⟨(a n,0),hp n⟩
  let q : ℕ→BoundaryTuning := fun n=>singletonBoundaryMap hK hf b hb0 hbk hb (p n)
  have he (n) : Chart.coefficients (q n).val=edgeCoefficients
      (Chart.rationalCosine j k) (Chart.rationalHeight j k) (a n) 0 :=
    singletonTuning_coefficients hK hf (p n)
  have ha : Tendsto a atTop atTop :=
    tendsto_atTop_add_const_right atTop (singletonRoof K j k b 0+1) tendsto_natCast_atTop_atTop
  have ht := source_location hK hf (fun n=>(q n).val) a 0 he
    (fun n=>(le_max_left _ _).trans_lt (hp n)) ha
  have hcl : (4*(Real.sin (Real.pi*j/k))^2,1)∈closure
      ((fun q : BoundaryTuning=>(q.val.y,q.val.beta)) ''
        singletonPlateau hK hf b hb0 hbk hb) := by
    apply mem_closure_of_tendsto (ht.2.2.1.prodMk_nhds ht.1)
    exact Eventually.of_forall (fun n=>⟨q n,⟨p n,rfl⟩,rfl⟩)
  have hnot : (4*(Real.sin (Real.pi*j/k))^2,1)∉
      ((fun q : BoundaryTuning=>(q.val.y,q.val.beta)) ''
        singletonPlateau hK hf b hb0 hbk hb) := by
    rintro ⟨r,_hr,heq⟩
    have hb1 := congrArg Prod.snd heq
    exact r.val.beta_lt_one.ne hb1
  rw [accPt_principal_iff_clusterPt,sdiff_singleton_eq_self hnot]
  exact mem_closure_iff_clusterPt.mp hcl

end polyak.FareyPlateau
