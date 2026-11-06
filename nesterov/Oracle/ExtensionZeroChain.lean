import nesterov.Oracle.ExtensionSmooth
import nesterov.Oracle.ExtensionFaces
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The canonical extension is a genuine first-order zero-chain.
Strict simplex support exclusion is passed to the coordinate face by
continuity of the actual gradient. -/
namespace nesterov.Oracle
noncomputable section
open Set Filter
open scoped Topology BigOperators

theorem moment_coordinate {I : Type*} [Fintype I] {d : ℕ}
    (v : I→EuclideanSpace ℝ (Fin d)) (α : I→ℝ) (m : Fin d) :
    moment v α m=∑ i,α i*(v i m) := by
  change (PiLp.projₗ (𝕜:=ℝ) 2 (fun _ : Fin d=>ℝ) m) (∑ i,α i • v i)=_
  rw [map_sum]
  simp only [map_smul,PiLp.projₗ_apply,smul_eq_mul]

namespace ExtensionData
variable {d : ℕ} (D : Oracle.ExtensionData (Fin (d+1)) (EuclideanSpace ℝ (Fin d)))

theorem continuous_field : Continuous D.field := by
  have h : LipschitzWith 1 D.field := LipschitzWith.of_dist_le_mul (fun x y=>by
    simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using D.field_lipschitz x y)
  exact h.continuous

theorem face_coordinate_zero {j m : Fin d} {y : EuclideanSpace ℝ (Fin d)}
    (hjm : j≠m) (hym : y m=0)
    (horder : ∀ k : Fin (d+1),j.val<k.val →∀ i,
      D.offsets k-inner ℝ (D.slopes k) (D.slopes i)/(1-D.q)≤
        D.offsets j.castSucc-inner ℝ (D.slopes j.castSucc) (D.slopes i)/(1-D.q))
    (horth : ∀ k : Fin (d+1),j.val<k.val →inner ℝ (D.slopes j.castSucc-D.slopes k) y=0)
    (hgap : ∀ k : Fin (d+1),j.val<k.val →0<D.slopes j.castSucc j-D.slopes k j)
    (hbefore : ∀ i : Fin (d+1),i.val≤j.val →D.slopes i m=0) : D.field y m=0 := by
  let e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single j 1
  have he : e m=0 := by simp [e,Ne.symm hjm]
  have hvanish (t : ℝ) (ht : 0<t) : D.field (y+t • e) m=0 := by
    have hzero (k : Fin (d+1)) (hk : j.val<k.val) : D.optimizer (y+t • e) k=0 := by
      apply D.optimizer_zero_of_separation (horder k hk)
      rw [inner_add_right,inner_smul_right,horth k hk,zero_add]
      have hi : inner ℝ (D.slopes j.castSucc-D.slopes k) e=
          D.slopes j.castSucc j-D.slopes k j := by
        simp [e,EuclideanSpace.inner_single_right,PiLp.sub_apply]
      rw [hi]
      exact mul_pos ht (hgap k hk)
    have hs : D.support (y+t • e) m=0 := by
      rw [support,moment_coordinate]
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : i.val≤j.val
      · rw [hbefore i hi,mul_zero]
      · rw [hzero i (lt_of_not_ge hi),zero_mul]
    change D.q*(y+t • e) m+D.support (y+t • e) m=0
    simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,hym,he,mul_zero,hs,add_zero]
  have heval : Continuous (fun z : EuclideanSpace ℝ (Fin d)=>z m) := PiLp.continuous_apply 2 (fun _ : Fin d=>ℝ) m
  have hpath : Continuous (fun t : ℝ=>y+t • e) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hc : ContinuousAt (fun t : ℝ=>D.field (y+t • e) m) 0 :=
    (heval.comp (D.continuous_field.comp hpath)).continuousAt
  have hl : Tendsto (fun t : ℝ=>D.field (y+t • e) m) (𝓝[>] (0:ℝ)) (𝓝 (D.field y m)) := by
    simpa only [zero_smul,add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun t : ℝ=>D.field (y+t • e) m) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hvanish t ht).symm
  exact tendsto_nhds_unique hl hz

theorem zero_chain
    (horder : ∀ j : Fin d,∀ k : Fin (d+1),j.val<k.val →∀ i,
      D.offsets k-inner ℝ (D.slopes k) (D.slopes i)/(1-D.q)≤
        D.offsets j.castSucc-inner ℝ (D.slopes j.castSucc) (D.slopes i)/(1-D.q))
    (hafter : ∀ j m : Fin d,j.val<m.val →D.slopes j.castSucc m=0)
    (hagree : ∀ j : Fin d,∀ k : Fin (d+1),j.val<k.val →∀ m : Fin d,
      m.val<j.val →D.slopes j.castSucc m=D.slopes k m)
    (hgap : ∀ j : Fin d,∀ k : Fin (d+1),j.val<k.val →0<D.slopes j.castSucc j-D.slopes k j)
    {j : Fin d} {y : EuclideanSpace ℝ (Fin d)} (hy : ∀ m : Fin d,j.val≤m.val →y m=0) :
    ∀ m : Fin d,j.val<m.val →D.field y m=0 := by
  intro m hm
  apply D.face_coordinate_zero (show j≠m by intro h;subst m;omega) (hy m hm.le)
    (horder j)
  · intro k hk
    rw [PiLp.inner_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i.val<j.val
    · have hh := hagree j k hk i hi
      simp only [PiLp.sub_apply,hh,sub_self,inner_zero_left]
    · have hh := hy i (le_of_not_gt hi)
      rw [hh,inner_zero_right]
  · exact hgap j
  · intro i hi
    let ii : Fin d := ⟨i.val,lt_of_le_of_lt hi j.isLt⟩
    have he : ii.castSucc=i := Fin.ext rfl
    rw [←he]
    exact hafter ii m (lt_of_le_of_lt hi hm)

end ExtensionData
end
end nesterov.Oracle
