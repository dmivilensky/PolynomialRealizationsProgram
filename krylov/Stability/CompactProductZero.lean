import krylov.Stability.CompactCoefficients
set_option autoImplicit false
/-!
Article: main_krylov, thm:dcs(c), compact C-one quadratic product estimate.
Use: bound a genuinely vanishing fresh defect times a genuinely vanishing
change of finite chronological weights by one compact-uniform quadratic term.
Source: the proved compact C-one mean-value estimate, the product-space
metric and the finite triangle inequality; no C-two hypothesis is used.
-/

namespace krylov.Stability
noncomputable section
open Set Metric Filter Topology
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]
variable {ι : Type*} [Fintype ι]

/-- A finite sum of diagonal-vanishing C-one weight changes times C-one
defects vanishing on a compact reference set has one genuine quadratic bound.
Use: freeze actual DC observed estimates in finite residual products while
keeping only the source's C-one regularity assumption.
Article: main_krylov, thm:dcs(c), compact-uniform O(omega squared).
Proof: the real C-one compact mean-value theorem gives a common linear bound
for each whole finite weight array on the diagonal compact set and for the
whole finite defect array on the original compact set. The finite triangle
inequality and true coordinate norm bounds multiply those two linear factors. -/
theorem compact_zero_product_sum (u : X × X → ι → ℝ) (d : X → ι → ℝ)
    (K : Set X) (hK : IsCompact K)
    (hu : ∀ x∈K,ContDiffAt ℝ 1 u (x,x)) (hd : ∀ x∈K,ContDiffAt ℝ 1 d x)
    (hu0 : ∀ x∈K,u (x,x)=0) (hd0 : ∀ x∈K,d x=0) :
    ∃ δ C : ℝ,0<δ ∧ 0≤C ∧ ∀ x∈K,∀ y : X,‖y-x‖≤δ →
      ‖∑ i,u (x,y) i*d y i‖≤C*‖y-x‖^2 := by
  let D : Set (X × X) := (fun x : X => (x,x)) '' K
  have hD : IsCompact D := hK.image (continuous_id.prodMk continuous_id)
  let U := interior {p : X × X | ContDiffAt ℝ 1 u p}
  let V := interior {x : X | ContDiffAt ℝ 1 d x}
  have hDU : D⊆U := by
    rintro _ ⟨x,hx,rfl⟩
    exact mem_interior_iff_mem_nhds.mpr ((hu x hx).eventually (by simp))
  have hKV : K⊆V := fun x hx => mem_interior_iff_mem_nhds.mpr ((hd x hx).eventually (by simp))
  obtain ⟨δu,Cu,hδu,hCu,hU⟩ := compact_local_lipschitz u U D isOpen_interior hD hDU
    (fun p hp => (show ContDiffAt ℝ 1 u p from interior_subset hp).contDiffWithinAt)
  obtain ⟨δd,Cd,hδd,hCd,hV⟩ := compact_local_lipschitz d V K isOpen_interior hK hKV
    (fun p hp => (show ContDiffAt ℝ 1 d p from interior_subset hp).contDiffWithinAt)
  refine ⟨min δu δd,(Fintype.card ι : ℝ)*Cu*Cd,lt_min hδu hδd,by positivity,?_⟩
  intro x hx y hy
  have hp : ‖(x,y)-(x,x)‖=‖y-x‖ := by simp only [Prod.sub_def,sub_self,Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _)]
  have hwu := hU (x,x) ⟨x,hx,rfl⟩ (x,y) (by rw [hp];exact hy.trans (min_le_left _ _))
  rw [hu0 x hx,sub_zero,hp] at hwu
  have hwd := hV x hx y (hy.trans (min_le_right _ _))
  rw [hd0 x hx,sub_zero] at hwd
  calc
    ‖∑ i,u (x,y) i*d y i‖≤∑ i,‖u (x,y) i*d y i‖ := norm_sum_le _ _
    _≤∑ _i : ι,(Cu*‖y-x‖)*(Cd*‖y-x‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul ((norm_le_pi_norm (u (x,y)) i).trans hwu)
        ((norm_le_pi_norm (d y) i).trans hwd) (norm_nonneg _) (by positivity)
    _=((Fintype.card ι : ℝ)*Cu*Cd)*‖y-x‖^2 := by
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      ring

end
end krylov.Stability
