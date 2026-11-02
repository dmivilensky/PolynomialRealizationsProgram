import krylov.Information.InnerMinimaxValue

/-!
Article: main_krylov, s4:cor-Q, genuine inner-class sharp minimax attainment.
Use: take the actual original pre-quadratic inner-source supremum and
genuine source-method infimum, proving the same sharp coefficient and
uniform cubic remainder with real RFC attainment for every profile.
Source: actual scaled admissible signed witnesses, true whole-source RFC
upper bound and complete-lattice source risk comparisons.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator MatrixOrder
variable {N : ℕ}

/-- The actual pre-quadratic inner-class minimax and RFC supremal risks have the original sharp coefficient with one uniform cubic bracket over all profiles.
Use: Prove genuine sharp minimax attainment inside Q ∩ S^natural, including every zero and degenerate profile.
Article: main_krylov, s4:cor-Q, genuine inner-class minimax attainment.
Proof: Fix the true whole-source RFC upper bound and real inner signed lower construction first. For each positive original radius, one common maximal-budget tube enforces the printed source slack, base-radius margin and reference domains. Every genuine strategy obeys the lower bound, while real RFC bounds the infimum above by its actual inner source supremum. -/
theorem inner_oneCorrection_minimax_bracket
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N) (hcount : referenceAtomCount A hA g=N+1) :
    ∃ r₀ : ℝ, 0<r₀ ∧ ∀ r : ℝ, 0<r → r≤r₀ →
      ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ (ω : ℕ → ℝ) (w μ : ℝ),
        0≤μ → μ≤δ → (∀ i<N, 0≤ω i ∧ ω i≤μ) → 0≤w → w≤μ →
        ENNReal.ofReal (sharpConstant (∑ i∈range N, ω i) w-C*μ^3)≤
          innerOneCorrectionMinimax A g r ω w μ ∧
        innerOneCorrectionMinimax A g r ω w μ≤
          innerWorstOutputRatio (rfcMethod fullMemory 1) A g r ω w μ ∧
        innerWorstOutputRatio (rfcMethod fullMemory 1) A g r ω w μ≤
          ENNReal.ofReal (sharpConstant (∑ i∈range N, ω i) w+C*μ^3) := by
  -- Choose the genuine outer RFC upper and inner signed-source lower bounds before all profiles.
  obtain ⟨r₀,δU,CU,hr₀,hδU,hCU,hupper⟩ := admissible_rfc_sharp_upper A hA g hN hcount
  obtain ⟨ε,CL,hε,hCL,hlower⟩ := innerWorstOutputRatio_sharp_lower A hA g hN hcount
  refine ⟨r₀,hr₀,?_⟩
  intro r hr hrr
  let b : ℝ := (N : ℝ)+1
  have hb : 0<b := by dsimp only [b]; positivity
  let δ := min δU (min (1/(2*b)) (min (r/((5+4*r)*b)) (min (ε/(2*b)) (1/(4*b^2)))))
  let C := CL*b^3+CU
  have hδ : 0<δ := by dsimp only [δ]; positivity
  have hC : 0<C := by dsimp only [C]; positivity
  refine ⟨δ,C,hδ,hC,?_⟩
  intro ω w μ hμ hμδ hω hw hwμ
  let W := ∑ i∈range N, ω i
  have hW : 0≤W := sum_nonneg fun i hi => (hω i (mem_range.mp hi)).1
  have hWμ : W≤(N : ℝ)*μ := by
    simpa only [sum_const,card_range,nsmul_eq_mul] using
      (sum_le_sum (fun i hi => (hω i (mem_range.mp hi)).2) : W≤∑ _i∈range N, μ)
  have hWb : W≤b*μ := by dsimp only [b]; nlinarith
  have hs : W+w≤b*μ := by dsimp only [b]; nlinarith
  have hμU : μ≤δU := hμδ.trans (min_le_left _ _)
  have hμhalf : μ≤1/(2*b) := hμδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hμr : μ≤r/((5+4*r)*b) := hμδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hμε : μ≤ε/(2*b) := hμδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hμslack : μ≤1/(4*b^2) := hμδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hshalf : W+w≤(1/2 : ℝ) := by
    have hh := (le_div_iff₀ (by positivity : 0<2*b)).mp hμhalf
    nlinarith
  have hmargin : (5+4*r)*W≤r := by
    have hh := (le_div_iff₀ (by positivity : 0<(5+4*r)*b)).mp hμr
    nlinarith [mul_le_mul_of_nonneg_left hWb (by positivity : 0≤5+4*r)]
  have hWε : W<ε := by
    have hh := (le_div_iff₀ (by positivity : 0<2*b)).mp hμε
    nlinarith
  have hslack : 4*((N : ℝ)+1)*W≤1 := by
    have hh := (le_div_iff₀ (by positivity : 0<4*b^2)).mp hμslack
    change 4*b*W≤1
    nlinarith [mul_le_mul_of_nonneg_left hWb (by positivity : 0≤4*b)]
  have hcube : CL*(W+w)^3≤C*μ^3 := by
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (add_nonneg hW hw) hs 3) hCL.le
    rw [mul_pow] at hp
    have hadd : 0≤CU*μ^3 := mul_nonneg hCU.le (pow_nonneg hμ 3)
    dsimp only [C]
    nlinarith
  refine ⟨?_,?_,?_⟩
  · apply le_iInf
    intro M
    exact (ENNReal.ofReal_le_ofReal (by linarith : sharpConstant W w-C*μ^3≤sharpConstant W w-CL*(W+w)^3)).trans
      (hlower M.method.policy M.consistent M.oneCorrection ω w μ r
        (fun i hi => (hω i hi).1) hw hμ hr.le hshalf hmargin hWε hslack)
  · exact iInf_le _ (rfcMinimaxStrategy _)
  · have ht := worstOutputRatio_le (rfcMethod fullMemory 1) A g N r ω w μ
      (sharpConstant W w+CU*μ^3)
      (fun S hS => hupper r hrr ω w μ μ hμ hμU (fun i hi => (hω i hi).2) hwμ le_rfl S hS)
    exact (innerWorstOutputRatio_le_outer _ _ _ _ _ _ _).trans (ht.trans
      (ENNReal.ofReal_le_ofReal (by dsimp only [C]; nlinarith [mul_nonneg hCL.le (mul_nonneg (pow_nonneg hb.le 3) (pow_nonneg hμ 3))])))


/-- The actual inner-subclass minimax and RFC supremal risks are finite and differ from the printed sharp coefficient by the same common cubic error.
Use: Give the original source asymptotic a genuine real value without an assumed bounded competitor risk.
Article: main_krylov, s4:cor-Q, genuine inner-class minimax attainment.
Proof: The actual extended-risk bracket proves finiteness of both source quantities. The reused real-risk bracket theorem then gives both absolute cubic estimates on the same genuine source tube. -/
theorem inner_oneCorrection_minimax_cubic {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1) :
    ∃ r₀ : ℝ, 0<r₀ ∧ ∀ r : ℝ, 0<r → r≤r₀ →
      ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ (ω : ℕ → ℝ) (w μ : ℝ),
        0≤μ → μ≤δ → (∀ i<N, 0≤ω i ∧ ω i≤μ) → 0≤w → w≤μ →
        innerOneCorrectionMinimax A g r ω w μ≠⊤ ∧
        innerWorstOutputRatio (rfcMethod fullMemory 1) A g r ω w μ≠⊤ ∧
        |(innerOneCorrectionMinimax A g r ω w μ).toReal-sharpConstant (∑ i∈range N, ω i) w|≤C*μ^3 ∧
        |(innerWorstOutputRatio (rfcMethod fullMemory 1) A g r ω w μ).toReal-
          sharpConstant (∑ i∈range N, ω i) w|≤C*μ^3 := by
  -- The same genuine bracket controls both actual source quantities, with no methodwise boundedness assumption.
  obtain ⟨r₀,hr₀,hbracket⟩ := inner_oneCorrection_minimax_bracket A hA g hN hcount
  refine ⟨r₀,hr₀,?_⟩
  intro r hr hrr
  obtain ⟨δ,C,hδ,hC,hbound⟩ := hbracket r hr hrr
  refine ⟨δ,C,hδ,hC,?_⟩
  intro ω w μ hμ hμδ hω hw hwμ
  obtain ⟨hl,hm,hu⟩ := hbound ω w μ hμ hμδ hω hw hwμ
  have hK : 0≤sharpConstant (∑ i∈range N, ω i) w :=
    sharpConstant_nonneg (sum_nonneg fun i hi => (hω i (mem_range.mp hi)).1) hw
  have he : 0≤C*μ^3 := mul_nonneg hC.le (pow_nonneg hμ 3)
  have hmin := realRisk_bracket hK he hl (hm.trans hu)
  have hrfc := realRisk_bracket hK he (hl.trans hm) hu
  exact ⟨hmin.1,hrfc.1,hmin.2,hrfc.2⟩

end
end krylov.Information
