import krylov.Information.BinaryPlanarAdmissible
import krylov.Information.AdmissibleUpper

/-!
Article: main_krylov, thm:H, the complete compatible-binary planar RFC upper bound.
Use: optimize over every tensor in the genuine binary ball and every
independent unknown beta in the source interval. Actual relative budgets
and the true own-base RFC execution are controlled by the already proved
original physical source theorem. Source: thm:C, the true binary slice norm,
and the elementary bound K(W,w)<=W^2/2+W*w.
-/

namespace krylov.Information
noncomputable section
open Real Matrix Finset krylov.Tensor krylov.Tensor.BinaryCubic krylov.Secant
  krylov.Reference krylov.LinearAlgebra krylov.Correction krylov.Methods
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ}

/-- Every nonnegative first/last budget lies below its actual total.
Article: main_krylov, thm:H, zero and coincident endpoint-budget cases included. -/
theorem binaryFirstLast_bounds (N j : ℕ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ binaryFirstLast N a b j ∧ binaryFirstLast N a b j ≤ a+b := by
  unfold binaryFirstLast
  split_ifs <;> constructor <;> linarith

/-- Actual RFC over the entire original compatible planar tensor ball and all unknown bases has the printed upper coefficient, uniformly with a linear relative source loss.
Article: main_krylov, thm:H, full supremum upper bound in the actual own-base normalization.
The constructed source is proved admissible from its true binary tensor and
beta; no desired response estimate, operator budget or trajectory is assumed. -/
theorem binaryPlanar_rfc_upper
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0 < N)
    (hcount : referenceAtomCount A hA g = N+1) (r : ℝ) (hr : 0 ≤ r) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 < C ∧
      ∀ κ e_c β : ℝ, 0 ≤ κ → κ ≤ e_c → e_c < ε₀ → |β| ≤ e_c →
      ∀ t : BinaryCubic, t.InBall →
      let e := canonicalCGUnitStep A g 0
      let h := canonicalCGUnitStep A g N
      let S := (binaryPlanarScenario e h κ r β N t).inPhysical (metricRoot A)⁻¹
      S.outputRatio (rfcMethod fullMemory 1) g N ≤
        (κ ^ 2 / 2 * (1+r) * (1+3*r)) * (1+C*e_c) := by
  obtain ⟨rb, δ, Cb, hrb, hδ, hCb, hupper⟩ := admissible_rfc_sharp_upper A hA g hN hcount
  let ε₀ := min rb (min (1/2) (δ / (2*(1+r))))
  have hε₀ : 0 < ε₀ := by dsimp only [ε₀]; positivity
  let C := 6 + 16*Cb*(1+r)^3
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨ε₀, C, hε₀, hC, ?_⟩
  intro κ e_c β hκ hκe hec hβ t ht
  let e := canonicalCGUnitStep A g 0
  let h := canonicalCGUnitStep A g N
  let S := (binaryPlanarScenario e h κ r β N t).inPhysical (metricRoot A)⁻¹
  have hec₀ : 0 ≤ e_c := hκ.trans hκe
  have hec₁ : e_c ≤ 1/2 := (hec.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hc : 0 < 1-e_c := by linarith
  have ho := canonicalCG_frame_of_full_atoms A hA g hcount
  have he : ‖e‖=1 := ho.norm_eq_one (0 : Fin (N+1))
  have hh : ‖h‖=1 := ho.norm_eq_one (Fin.last N)
  have heh : inner ℝ e h=0 := ho.inner_eq_zero (i := 0) (j := Fin.last N)
    (by intro hz; have hv := congrArg Fin.val hz; simp only [Fin.val_zero, Fin.val_last] at hv; omega)
  have hS := physical_binaryPlanarScenario_admissible A hA e h he hh heh κ r β e_c
    hκ hr hec₀ (by linarith) hβ N t ht
  let ω := fun j => binaryFirstLast N κ (κ*r) j / (1-e_c)
  let w := κ*r/(1-e_c)
  let μ := 2*κ*(1+r)
  have hμ : 0 ≤ μ := by dsimp only [μ]; positivity
  have hμδ : μ ≤ δ := by
    have hε := (lt_div_iff₀ (by positivity : 0 < 2*(1+r))).mp
      (hec.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    dsimp only [μ]
    nlinarith only [mul_le_mul_of_nonneg_right hκe (by positivity : 0 ≤ 2*(1+r)), hε]
  have hbudget (x : ℝ) (hx : x ≤ κ*(1+r)) : x/(1-e_c) ≤ μ := by
    apply (div_le_iff₀ hc).mpr
    have hb := mul_le_mul_of_nonneg_left hec₁ (mul_nonneg hκ (by positivity : 0 ≤ 1+r))
    dsimp only [μ]
    nlinarith only [hx, hb]
  have hω (j : ℕ) (_hj : j<N) : ω j ≤ μ := by
    apply hbudget
    exact (binaryFirstLast_bounds N j κ (κ*r) hκ (mul_nonneg hκ hr)).2.trans_eq (by ring)
  have hw : w ≤ μ := hbudget _ (by nlinarith only [hκ])
  have hu := hupper e_c (hec.trans_le (min_le_left _ _)).le ω w 0 μ hμ hμδ hω hw hμ S hS
  have hsum : (∑ j ∈ range N, ω j) = κ*(1+r)/(1-e_c) := by
    dsimp only [ω]
    rw [← Finset.sum_div, binaryFirstLast_sum N hN]
    congr 1
    ring
  rw [hsum] at hu
  have hk := sharpConstant_upper
    (div_nonneg (mul_nonneg hκ (by positivity : 0 ≤ 1+r)) hc.le)
    (div_nonneg (mul_nonneg hκ hr) hc.le)
  let R := (1+r)*(1+3*r)/2
  have hR : 1/2 ≤ R := by dsimp only [R]; nlinarith [sq_nonneg r]
  have hK : sharpConstant (κ*(1+r)/(1-e_c)) w ≤ κ^2*R/(1-e_c)^2 := by
    exact hk.trans_eq (by dsimp only [w, R]; field_simp; ring)
  have hinv : 1/(1-e_c)^2 ≤ 1+6*e_c := by
    apply (div_le_iff₀ (sq_pos_of_pos hc)).mpr
    have hn : 0 ≤ e_c*(1-2*e_c)*(4-3*e_c) := by
      apply mul_nonneg (mul_nonneg hec₀ (by linarith))
      linarith
    nlinarith only [hn]
  have hleading : κ^2*R/(1-e_c)^2 ≤ κ^2*R*(1+6*e_c) := by
    have hh := mul_le_mul_of_nonneg_left hinv (mul_nonneg (sq_nonneg κ) (by linarith : 0 ≤ R))
    simpa only [div_eq_mul_inv, mul_one, one_mul] using hh
  have hrem : Cb*μ^3 ≤ κ^2*R*(16*Cb*(1+r)^3*e_c) := by
    have hκ3 := mul_le_mul_of_nonneg_left hκe (sq_nonneg κ)
    have h1 := mul_le_mul_of_nonneg_left hκ3 (by positivity : 0 ≤ 8*Cb*(1+r)^3)
    have h2 := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 16*Cb*(1+r)^3*κ^2*e_c)
    dsimp only [μ]
    nlinarith only [h1, h2]
  apply hu.trans
  calc
    _ ≤ κ^2*R/(1-e_c)^2 + Cb*μ^3 := add_le_add hK le_rfl
    _ ≤ κ^2*R*(1+6*e_c) + κ^2*R*(16*Cb*(1+r)^3*e_c) := add_le_add hleading hrem
    _ = _ := by dsimp only [R, C]; ring

end
end krylov.Information
