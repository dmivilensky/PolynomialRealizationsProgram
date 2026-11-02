import krylov.Functions.PlanarRFCFOriginalBaseAverage

/-!
Article: main_krylov, thm:Fplanar, the literal printed relative C_Y equality.
Use: express the genuine original independent-base supremum with the exact
2(1-delta) tensor budget and its uniform relative 1+O(p) source loss.
Source: the proved fourth-order actual-solve remainder, positivity of the
true C_Y coefficient and its sharp original binary-ball bounds.
-/
namespace krylov.Functions
noncomputable section
open krylov.Tensor.BinaryCubic

/-- The printed RFC-F planar equality, with the original tensor budget,
independent original |beta|≤B*p, actual observed-model solves, exact C_Y
and the printed two-sided constants. Article: main_krylov, thm:Fplanar. -/
theorem planeUnknownBaseRFCF_printed_equality (r B δ : ℝ)
    (hr : 0<r) (hB : 0≤B) (hδ : 0<δ ∧ δ<1) :
    (2*r≤modelMetricCoefficient r ∧ modelMetricCoefficient r≤2*r*Real.sqrt (1+r^2)) ∧
    ∃ ep C : ℝ, 0<ep ∧ 0<C ∧ ∀ p : ℝ, 0<p → p<ep →
      |planeUnknownBaseScaledRFCFActualWorst p r B (2*(1-δ))/
        ((1-δ)^2*r*modelMetricCoefficient r*p^3)-1|≤C*p := by
  refine ⟨modelMetricCoefficient_bounds hr.le,?_⟩
  have ha : 0<2*(1-δ) := by linarith only [hδ.2]
  obtain ⟨ep,C,hep,hC,hrem⟩ := planeUnknownBaseScaledRFCFActualWorst_remainder r B (2*(1-δ)) hr hB ha
  let K := (1-δ)^2*r*modelMetricCoefficient r
  have hCY : 0<modelMetricCoefficient r := lt_of_lt_of_le (by positivity : 0<2*r) (modelMetricCoefficient_bounds hr.le).1
  have hK : 0<K := by dsimp only [K]; exact mul_pos (mul_pos (sq_pos_of_ne_zero (by linarith only [hδ.2])) hr) hCY
  refine ⟨ep,C/K,hep,div_pos hC hK,?_⟩
  intro p hp he
  have hb := hrem p hp he
  have hcoeff : (2*(1-δ))^2*r/4*modelMetricCoefficient r=K := by dsimp only [K]; ring
  rw [hcoeff] at hb
  change |planeUnknownBaseScaledRFCFActualWorst p r B (2*(1-δ))/(K*p^3)-1|≤(C/K)*p
  have hden : 0<K*p^3 := mul_pos hK (pow_pos hp 3)
  have heq : planeUnknownBaseScaledRFCFActualWorst p r B (2*(1-δ))/(K*p^3)-1=
      (planeUnknownBaseScaledRFCFActualWorst p r B (2*(1-δ))-K*p^3)/(K*p^3) := by field_simp
  rw [heq,abs_div,abs_of_pos hden]
  apply (div_le_iff₀ hden).mpr
  exact hb.trans_eq (by field_simp)

end
end krylov.Functions
