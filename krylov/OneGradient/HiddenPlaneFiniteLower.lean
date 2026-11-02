import krylov.OneGradient.HiddenPlaneLeading
import krylov.OneGradient.TwoModelReferenceLower
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(c), finite attained four-adversary lower bound.
Use: the genuine V2 maximizer forces its coefficient at arbitrary separate
common-data outputs, with a uniform explicit reference-normalized loss.
Source: actual hidden-entry matrices, exact observed column seminorm,
real norm budgets and the finite arbitrary-output reference game.
-/

namespace krylov.OneGradient
noncomputable section
open krylov.Reference krylov.LinearAlgebra krylov.Information
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The actual hidden-entry maximizer forces the full V2 coefficient
in the genuine opposite-centre games at arbitrary common-data outputs.
The explicit loss tends to one with omega; no output-rate, regularity,
query independence or limiting-policy hypothesis is imposed.
Use: original arbitrary-M1 lower bounds retain the true query length
and reference mismatch until their genuine geometric relation is used.
Article: main_krylov, thm:local(c), finite sharp hidden-plane obstruction.
Proof: choose the real attained closed-disc maximizer. Its true centre
and rank-one half-width obey actual operator budgets. The exact observed
column seminorm is the query length times V2 omega². Apply the genuine
finite four-model reference inequality at both arbitrary outputs. -/
theorem hiddenPlane_finite_reference_lower
    (e h : EuclideanSpace ℝ (Fin n)) (he : ‖e‖=1) (hh : ‖h‖=1) (heh : inner ℝ e h=0)
    (r : EuclideanSpace ℝ (Fin n)) (W w omega q sigma : ℝ)
    (hW : 0< W) (hw : 0< w) (homega : 0< omega) (hq : 0≤ q)
    (hgeom : sigma≤ q+‖r‖) :
    ∃ a g : ℝ,0< a ∧ 0≤ g ∧ a^2+g^2≤1 ∧
      twoDimensionalHiddenValue W w a g=twoDimensionalValue W w ∧
      let eta := W*omega
      let radius := w*omega
      let S := planarMatrix e h (hiddenPlaneCentre a g) a g
      let D := cgOperator (eta • planarMatrix e h (hiddenPlaneHalfWidth a g) 0 0)
      let Cp := cgOperator (1+eta • S)
      let Cm := cgOperator (1-eta • S)
      let z := (eta*q) • cgOperator S h
      ∀ up um : EuclideanSpace ℝ (Fin n),
        (twoDimensionalValue W w*omega^2)*sigma≤
          (1+(eta+radius)+(eta+radius)*eta/radius+
            (twoDimensionalValue W w*omega^2)/radius*(1+eta+radius))*
          max (twoModelRisk Cp D (r+z) up radius) (twoModelRisk Cm D (r-z) um radius) := by
  obtain ⟨a,g,ha,hg,hd,hvalue⟩ := twoDimensional_hidden_attained W w hW hw.le
  refine ⟨a,g,ha,hg,hd,hvalue,?_⟩
  let eta := W*omega
  let radius := w*omega
  let S := planarMatrix e h (hiddenPlaneCentre a g) a g
  let H := planarMatrix e h (hiddenPlaneHalfWidth a g) 0 0
  let D := cgOperator (eta • H)
  let Cp := cgOperator (1+eta • S)
  let Cm := cgOperator (1-eta • S)
  let z := (eta*q) • cgOperator S h
  have heta : 0≤ eta := (mul_pos hW homega).le
  have hradius : 0< radius := mul_pos hw homega
  have hwidth := hiddenPlane_halfWidth_bounds a g ha hd
  have hSn : ‖S‖≤1 := by
    simpa only [zero_mul,add_zero] using hiddenPlane_completion_bound e h he hh heh a g 0 hd (by norm_num)
  have hTn : ‖cgOperator S‖≤1 := by
    rw [show ‖cgOperator S‖=‖S‖ from (Matrix.l2_opNorm_toEuclideanCLM S).symm]
    exact hSn
  have hHn : ‖H‖≤1 := by rw [planar_diagonal_norm e h he,abs_of_nonneg hwidth.1];exact hwidth.2
  have hDn : ‖D‖≤ eta := by
    rw [show ‖D‖=‖eta • H‖ from (Matrix.l2_opNorm_toEuclideanCLM _).symm,norm_smul,Real.norm_of_nonneg heta]
    exact (mul_le_mul_of_nonneg_left hHn heta).trans_eq (mul_one _)
  have hpc : Cp-ContinuousLinearMap.id ℝ _=eta • cgOperator S := by
    simp only [Cp,cgOperator,map_add,map_one,map_smul]
    change (ContinuousLinearMap.id ℝ _+eta • cgOperator S)-ContinuousLinearMap.id ℝ _=_
    abel
  have hmc : Cm-ContinuousLinearMap.id ℝ _= -(eta • cgOperator S) := by
    simp only [Cm,cgOperator,map_sub,map_one,map_smul]
    change (ContinuousLinearMap.id ℝ _-eta • cgOperator S)-ContinuousLinearMap.id ℝ _=_
    abel
  have hclosep : ‖Cp-ContinuousLinearMap.id ℝ _‖≤ eta := by
    rw [hpc,norm_smul,Real.norm_of_nonneg heta]
    exact (mul_le_mul_of_nonneg_left hTn heta).trans_eq (mul_one _)
  have hclosem : ‖Cm-ContinuousLinearMap.id ℝ _‖≤ eta := by
    rw [hmc,norm_neg,norm_smul,Real.norm_of_nonneg heta]
    exact (mul_le_mul_of_nonneg_left hTn heta).trans_eq (mul_one _)
  have hnorm (C : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (hC : ‖C-ContinuousLinearMap.id ℝ _‖≤ eta) : ‖C‖≤1+eta := by
    have hsum := norm_add_le (C-ContinuousLinearMap.id ℝ _) (ContinuousLinearMap.id ℝ _)
    rw [sub_add_cancel] at hsum
    linarith [ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))]
  have hV : 0≤ twoDimensionalValue W w := by
    unfold twoDimensionalValue
    split_ifs <;> positivity
  have hlead : (twoDimensionalValue W w*omega^2)*q≤‖D z‖+radius*‖z‖ := by
    have heq := hiddenPlane_leading_coefficient e h he hh heh a g W w omega q ha hd hW.le homega.le hq
    change ‖D z‖+radius*‖z‖=q*omega^2*twoDimensionalHiddenValue W w a g at heq
    rw [hvalue] at heq
    exact le_of_eq (by rw [heq];ring)
  dsimp only
  intro up um
  exact twoModelRisk_uniform_reference_lower Cp Cm D r z up um eta radius
    (twoDimensionalValue W w*omega^2) q sigma heta hradius (mul_nonneg hV (sq_nonneg omega))
    hDn hclosep hclosem (hnorm Cp hclosep) (hnorm Cm hclosem) hgeom hlead

end
end krylov.OneGradient
