import krylov.Information.FrobeniusMinimaxValue

/-!
Article: Proposition B.22 [thm:C2] of krylov.tex.
Use: both unknown-base and exactly-known-base source minimax risks, and
actual RFC's supremum, have the same sharp K/√2 cubic bracket.
Source: actual admissible fixed-base lower witnesses, full physical
Frobenius upper bounds and genuine source-class infimum comparisons.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant
  krylov.Correction krylov.Methods
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
/-- Both genuine physical Frobenius minimax values and RFC's actual worst-source risks have the sharp K/√2 bracket with one common all-profile cubic loss.
Use: the sharp source norm variant is proved for the real infimum–supremum, already with exactly known base, including every degenerate profile.
Article: main_krylov, thm:C2(a), actual norm-sensitive minimax bracket and RFC attainment.
Proof: fix the actual full-class physical RFC tube first. The same genuine
known-base signed pair forces every source strategy's lower coefficient in
both scenario classes. The finite profile sum is at most N times its
largest budget, making the loss uniformly cubic. Actual full-memory RFC
is a genuine source-class strategy, so its true supremum bounds the infimum
above and obeys the sharp physical Frobenius upper estimate.
-/
theorem frobenius_minimax_bracket {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1) :
    ∃ r₀ δ C : ℝ, 0<r₀ ∧ 0<δ ∧ 0<C ∧ ∀ (r : ℝ), 0≤r → r≤r₀ → ∀ known : Bool,
      ∀ (ω : ℕ → ℝ) (w μ : ℝ), 0≤μ → μ≤δ → (∀ i<N, 0≤ω i ∧ ω i≤μ) → 0≤w → w≤μ →
        ENNReal.ofReal (sharpConstant (∑ i∈range N, ω i) w/Real.sqrt 2-C*μ^3)≤
          frobeniusMinimax known A g N r ω w μ ∧
        frobeniusMinimax known A g N r ω w μ≤
          frobeniusWorstOutputRatio known (rfcMethod fullMemory 1) A g N r ω w μ ∧
        frobeniusWorstOutputRatio known (rfcMethod fullMemory 1) A g N r ω w μ≤
          ENNReal.ofReal (sharpConstant (∑ i∈range N, ω i) w/Real.sqrt 2+C*μ^3) := by
  -- The true source constants precede both knowledge regimes, every method and every primitive profile.
  obtain ⟨r₀,δU,CU,hr₀,hδU,hCU,hupper⟩ := admissible_frobenius_rfc_sharp_upper A hA g hN hcount
  let b : ℝ := N+1
  have hb : 0<b := by dsimp only [b]; positivity
  let δ := min δU (1/(2*b))
  let C := 2*b^3+CU
  have hδ : 0<δ := lt_min hδU (by positivity)
  have hC : 0<C := by dsimp only [C]; positivity
  refine ⟨r₀,δ,C,hr₀,hδ,hC,?_⟩
  intro r hr hrr known ω w μ hμ hμδ hω hw hwμ
  let W := ∑ i∈range N, ω i
  have hW : 0≤W := sum_nonneg fun i hi => (hω i (mem_range.mp hi)).1
  have hWμ : W≤(N : ℝ)*μ := by
    simpa only [sum_const,card_range,nsmul_eq_mul] using
      (sum_le_sum (fun i hi => (hω i (mem_range.mp hi)).2) : W≤∑ _i∈range N, μ)
  have hs : W+w≤b*μ := by dsimp only [b]; nlinarith
  have hμU : μ≤δU := hμδ.trans (min_le_left _ _)
  have hμhalf : μ≤1/(2*b) := hμδ.trans (min_le_right _ _)
  have hshalf : W+w≤(1/2 : ℝ) := by
    have hh := (le_div_iff₀ (by positivity : 0<2*b)).mp hμhalf
    nlinarith
  have hcube : 2*(W+w)^3≤C*μ^3 := by
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (add_nonneg hW hw) hs 3) (by norm_num : (0 : ℝ)≤2)
    rw [mul_pow] at hp
    have hadd : 0≤CU*μ^3 := mul_nonneg hCU.le (pow_nonneg hμ 3)
    dsimp only [C]
    nlinarith
  refine ⟨?_,?_,?_⟩
  · apply le_iInf
    intro M
    exact (ENNReal.ofReal_le_ofReal (by linarith : sharpConstant W w/Real.sqrt 2-C*μ^3≤
      sharpConstant W w/Real.sqrt 2-2*(W+w)^3)).trans
      (frobeniusWorst_sharp_lower A hA g hN hcount known M.method.policy M.consistent M.oneCorrection
        ω w μ r (fun i hi => (hω i hi).1) hw hμ hr hshalf)
  · exact iInf_le _ (rfcMinimaxStrategy _)
  · unfold frobeniusWorstOutputRatio
    apply iSup_le
    intro S
    have ht := hupper r hrr ω w μ μ hμ hμU (fun i hi => (hω i hi).2) hwμ le_rfl S.val S.property.1
    apply ENNReal.ofReal_le_ofReal (ht.trans _)
    have hc : CU≤C := le_add_of_nonneg_left (by dsimp only [b]; positivity)
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hc (pow_nonneg hμ 3))


/-- The actual Frobenius minimax value and RFC worst-source risk are finite and differ from K/√2 by at most the same uniform cubic amount, with unknown or exactly known base.
Use: read the full source norm variant as an ordinary real asymptotic after deriving finiteness of its actual infimum–supremum.
Article: main_krylov, thm:C2(a), complete real all-profile Frobenius minimax bound.
Proof: the genuine common source bracket controls both actual risks. Its
finite upper endpoint proves actual finiteness, and exact nonnegative real
normalization gives the two sharp-coefficient cubic absolute-error estimates.
-/
theorem frobenius_minimax_cubic {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1) :
    ∃ r₀ δ C : ℝ, 0<r₀ ∧ 0<δ ∧ 0<C ∧ ∀ (r : ℝ), 0≤r → r≤r₀ → ∀ known : Bool,
      ∀ (ω : ℕ → ℝ) (w μ : ℝ), 0≤μ → μ≤δ → (∀ i<N, 0≤ω i ∧ ω i≤μ) → 0≤w → w≤μ →
        frobeniusMinimax known A g N r ω w μ≠⊤ ∧
        frobeniusWorstOutputRatio known (rfcMethod fullMemory 1) A g N r ω w μ≠⊤ ∧
        |(frobeniusMinimax known A g N r ω w μ).toReal-sharpConstant (∑ i∈range N, ω i) w/Real.sqrt 2|≤C*μ^3 ∧
        |(frobeniusWorstOutputRatio known (rfcMethod fullMemory 1) A g N r ω w μ).toReal-
          sharpConstant (∑ i∈range N, ω i) w/Real.sqrt 2|≤C*μ^3 := by
  -- The same genuine bracket works before both knowledge regimes and every source budget profile.
  obtain ⟨r₀,δ,C,hr₀,hδ,hC,hbound⟩ := frobenius_minimax_bracket A hA g hN hcount
  refine ⟨r₀,δ,C,hr₀,hδ,hC,?_⟩
  intro r hr hrr known ω w μ hμ hμδ hω hw hwμ
  obtain ⟨hl,hm,hu⟩ := hbound r hr hrr known ω w μ hμ hμδ hω hw hwμ
  have hK : 0≤sharpConstant (∑ i∈range N, ω i) w/Real.sqrt 2 :=
    div_nonneg (sharpConstant_nonneg (sum_nonneg fun i hi => (hω i (mem_range.mp hi)).1) hw) (Real.sqrt_nonneg 2)
  have he : 0≤C*μ^3 := mul_nonneg hC.le (pow_nonneg hμ 3)
  have hmin := realRisk_bracket hK he hl (hm.trans hu)
  have hrfc := realRisk_bracket hK he (hl.trans hm) hu
  exact ⟨hmin.1,hrfc.1,hmin.2,hrfc.2⟩


end
end krylov.Information
