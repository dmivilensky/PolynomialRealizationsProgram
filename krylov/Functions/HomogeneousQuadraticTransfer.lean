import krylov.Functions.HomogeneousCycleTransfer

/-!
Article: main_krylov, lem:cycle-transfer, arbitrary-degree improved remainder.
Use: prove the extra big-O order from genuine quadratic input jets and a
genuine operator Taylor remainder. Source: true continuous multilinear
telescoping, exact homogeneity and the triangle inequality.
-/
namespace krylov.Functions
noncomputable section
open Set
variable {d : ℕ} {ι V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Quadratic true source jets and an independent order-(d+1) operator
Taylor bound give an actual order-(d+2) rescaled response remainder,
uniformly over the whole reference family. Article: lem:cycle-transfer. -/
theorem homogeneous_cycle_transfer_quadratic
    (F : ι → V → W) (P : ι → ContinuousMultilinearMap ℝ (fun _ : Fin d => V) W)
    (x : ℝ → ι → V) (v : ι → V) (U : Set ι) (B C J A : ℝ)
    (hB : 0≤B) (hC : 0≤C) (hJ : 0≤J) (hA : 0≤A)
    (hP : ∀ u∈U, ‖P u‖≤C) (hv : ∀ u∈U, ‖v u‖≤B)
    (hx : ∃ ex : ℝ, 0<ex ∧ ∀ ε : ℝ, 0<ε → ε<ex → ∀ u∈U, ‖x ε u‖≤B*ε)
    (hjet : ∃ ej : ℝ, 0<ej ∧ ∀ ε : ℝ, 0<ε → ε<ej → ∀ u∈U,
      ‖x ε u-ε • v u‖≤J*ε^2)
    (hop : ∃ δ : ℝ, 0<δ ∧ ∀ u∈U, ∀ z : V, ‖z‖<δ →
      ‖F u z-homogeneousResponse (P u) z‖≤A*‖z‖^(d+1)) :
    ∃ ep C₀ : ℝ, 0<ep ∧ 0≤C₀ ∧ ∀ ε : ℝ, 0<ε → ε<ep → ∀ u∈U,
      ‖rescaledOperatorOutput F x ε u-ε^(d+1) • homogeneousResponse (P u) (v u)‖≤C₀*ε^(d+2) := by
  obtain ⟨ex,hex,hxb⟩ := hx
  obtain ⟨ej,hej,hjb⟩ := hjet
  obtain ⟨δ,hδ,hopb⟩ := hop
  let C₀ := A*B^(d+1)+C*d*B^(d-1)*J
  refine ⟨min ex (min ej (δ/(B+1))),C₀,by positivity,by dsimp only [C₀]; positivity,?_⟩
  intro ε hε he u hu
  have hxe := hxb ε hε (he.trans_le (min_le_left _ _)) u hu
  have hje := hjb ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu
  have hsmall : ‖x ε u‖<δ := by
    have hh := (lt_div_iff₀ (by positivity : 0<B+1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith only [hxe,hh,hε]
  have hpoly : ‖homogeneousResponse (P u) (x ε u)-ε^d • homogeneousResponse (P u) (v u)‖≤
      (C*d*B^(d-1)*J)*ε^(d+1) := by
    have hh := homogeneousResponse_jet_bound (P u) (x ε u) (v u) ε B (J*ε)
      hε hB hxe (hv u hu) (by nlinarith only [hje])
    have hb : ‖P u‖*d*B^(d-1)*(J*ε)≤C*d*B^(d-1)*(J*ε) := by gcongr; exact hP u hu
    exact hh.trans ((mul_le_mul_of_nonneg_right hb (pow_nonneg hε.le d)).trans_eq (by rw [pow_succ]; ring))
  have ho : ‖F u (x ε u)-homogeneousResponse (P u) (x ε u)‖≤(A*B^(d+1))*ε^(d+1) := by
    calc
      _ ≤ A*‖x ε u‖^(d+1) := hopb u hu _ hsmall
      _ ≤ A*(B*ε)^(d+1) := by gcongr
      _ = _ := by rw [mul_pow]; ring
  have hsum : ‖F u (x ε u)-ε^d • homogeneousResponse (P u) (v u)‖≤C₀*ε^(d+1) := by
    have heq : F u (x ε u)-ε^d • homogeneousResponse (P u) (v u)=
        (F u (x ε u)-homogeneousResponse (P u) (x ε u))+
          (homogeneousResponse (P u) (x ε u)-ε^d • homogeneousResponse (P u) (v u)) := by abel
    rw [heq]
    exact (norm_add_le _ _).trans ((add_le_add ho hpoly).trans_eq (by dsimp only [C₀]; ring))
  have heq : rescaledOperatorOutput F x ε u-ε^(d+1) • homogeneousResponse (P u) (v u)=
      ε • (F u (x ε u)-ε^d • homogeneousResponse (P u) (v u)) := by
    simp only [rescaledOperatorOutput,smul_sub,smul_smul,pow_succ]
    congr 2
    ring
  rw [heq,norm_smul,Real.norm_of_nonneg hε.le]
  exact (mul_le_mul_of_nonneg_left hsum hε.le).trans_eq (by rw [show d+2=(d+1)+1 by omega,pow_succ]; ring)

end
end krylov.Functions
