import polyak.FareyPlateau.Domain.Source
import Mathlib.Analysis.Convex.Topology

/-! The topological argument for the single connected plateau works
without assuming that a_F is continuous. A continuous finite majorant
suffices because every vertical section is an upper ray. -/
noncomputable section
namespace polyak.FareyPlateau
open Set

def upperRoof (f : ℝ→ℝ) : Set (ℝ×ℝ) := {p | f p.2<p.1}

theorem continuous_roof_connected {g : ℝ→ℝ} (hg : Continuous g) :
    IsConnected (upperRoof g) := by
  let S : Set (ℝ×ℝ) := {p | 0<p.2}
  have hS : Convex ℝ S := by
    intro p hp q hq a b ha hb hab
    change 0<a*p.2+b*q.2
    have hp' : 0<p.2 := hp
    have hq' : 0<q.2 := hq
    rcases lt_or_eq_of_le ha with ha|rfl
    · exact add_pos_of_pos_of_nonneg (mul_pos ha hp') (mul_nonneg hb hq'.le)
    · have hb1 : b=1 := by linarith
      simp [hb1,hq']
  have hSc : IsConnected S := ⟨⟨(0,1),by norm_num [S]⟩,hS.isPreconnected⟩
  let F := fun p : ℝ×ℝ=>(g p.1+p.2,p.1)
  have hF : Continuous F :=
    ((hg.comp continuous_fst).add continuous_snd).prodMk continuous_fst
  have him : F '' S=upperRoof g := by
    ext p
    constructor
    · rintro ⟨x,hx,rfl⟩
      change g x.1<g x.1+x.2
      change 0<x.2 at hx
      linarith
    · intro hp
      refine ⟨(p.2,p.1-g p.2),?_,?_⟩
      · change 0<p.1-g p.2
        exact sub_pos.mpr hp
      · dsimp [F]
        ext <;> simp
  rw [←him]
  exact hSc.image F hF.continuousOn

theorem bounded_roof_connected {f g : ℝ→ℝ} (hg : Continuous g)
    (hbound : ∀D,f D≤g D) : IsConnected (upperRoof f) := by
  let B := upperRoof g
  let V := fun D : ℝ=>{p : ℝ×ℝ | p.2=D ∧ f D<p.1}
  have hB : IsConnected B := continuous_roof_connected hg
  have hsub : B⊆upperRoof f := fun p hp=>(hbound p.2).trans_lt hp
  have hV (D : ℝ) : IsPreconnected (V D) := by
    have him : (fun a : ℝ=>(a,D)) '' Ioi (f D)=V D := by
      ext p
      constructor
      · rintro ⟨a,ha,rfl⟩; exact ⟨rfl,ha⟩
      · rintro ⟨he,hp⟩; refine ⟨p.1,hp,?_⟩; ext <;> simp [he]
    rw [←him]
    exact isPreconnected_Ioi.image _ (continuous_id.prodMk continuous_const).continuousOn
  have hBV (D : ℝ) : IsPreconnected (B∪V D) := by
    apply IsPreconnected.union' _ hB.isPreconnected (hV D)
    refine ⟨(g D+1,D),?_,?_⟩
    · change g D<g D+1; linarith
    · refine ⟨rfl,?_⟩
      linarith [hbound D]
  have him : (⋃D : ℝ,B∪V D)=upperRoof f := by
    ext p
    constructor
    · intro hp
      obtain ⟨D,hD⟩ := mem_iUnion.mp hp
      rcases hD with hD|hD
      · exact hsub hD
      · change f p.2<p.1
        rw [hD.1]
        exact hD.2
    · intro hp
      exact mem_iUnion.mpr ⟨p.2,Or.inr ⟨rfl,hp⟩⟩
  refine ⟨⟨(g 0+1,0),?_⟩,?_⟩
  · change f 0<g 0+1
    linarith [hbound 0]
  · rw [←him]
    apply isPreconnected_iUnion _ hBV
    refine ⟨(g 0+1,0),?_⟩
    exact mem_iInter.mpr (fun _=>Or.inl (by change g 0<g 0+1; linarith))

end polyak.FareyPlateau
