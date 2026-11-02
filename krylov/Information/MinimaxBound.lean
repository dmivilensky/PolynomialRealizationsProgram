import krylov.Information.MinimaxValue

/-!
Article: Theorem 3.3 [thm:C] of krylov.tex.
Use: bracket the actual infimum of actual physical scenario suprema and
the actual RFC supremum by K with one uniform all-profile cubic error.
Source: admissible lower pairs, the derived full reference ball and the
actual full-class RFC bound; complete-lattice comparisons preserve both.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant
  krylov.Correction krylov.Methods
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
/-- The genuine unknown-base minimax risk is bracketed by the sharp coefficient with one cubic error, and the actual RFC source supremum obeys the same bracket.
Use: this is the complete quantitative all-profile infimum–supremum assertion, with constants fixed before every method and profile.
Article: main_krylov, thm:C, actual unknown-base second-order minimax and RFC attainment.
Proof: the derived genuine reference ball gives the full physical RFC upper
bound. For each fixed positive source radius, shrink the common profile
radius until the explicit signed witnesses fit that ball and its genuine
normalization tube. The finite profile sum is at most N times its largest
budget. Thus the true method-uniform cubic lower loss is at most C μ³.
Every real source strategy obeys that lower bound, while the actual admissible
RFC strategy bounds the infimum above by its own genuine source supremum.
-/
theorem oneCorrection_minimax_bracket {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1) :
    ∃ r₀ : ℝ, 0<r₀ ∧ ∀ r : ℝ, 0<r → r≤r₀ →
      ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ (ω : ℕ → ℝ) (w μ : ℝ),
        0≤μ → μ≤δ → (∀ i<N, 0≤ω i ∧ ω i≤μ) → 0≤w → w≤μ →
        ENNReal.ofReal (sharpConstant (∑ i∈range N, ω i) w-C*μ^3)≤
          oneCorrectionMinimax A g N r ω w μ ∧
        oneCorrectionMinimax A g N r ω w μ≤
          worstOutputRatio (rfcMethod fullMemory 1) A g N r ω w μ ∧
        worstOutputRatio (rfcMethod fullMemory 1) A g N r ω w μ≤
          ENNReal.ofReal (sharpConstant (∑ i∈range N, ω i) w+C*μ^3) := by
  -- Fix both genuine source bounds before choosing the source ball radius or any profile.
  obtain ⟨r₀,δU,CU,hr₀,hδU,hCU,hupper⟩ := admissible_rfc_sharp_upper A hA g hN hcount
  obtain ⟨ε,CL,hε,hCL,hlower⟩ := worstOutputRatio_sharp_lower A hA g hN hcount
  refine ⟨r₀,hr₀,?_⟩
  intro r hr hrr
  let b : ℝ := N+1
  have hb : 0<b := by dsimp only [b]; positivity
  let δ := min δU (min (1/(2*b)) (min (r/b) (ε/(2*b))))
  let C := CL*b^3+CU
  have hδ : 0<δ := lt_min hδU (lt_min (by positivity) (lt_min (div_pos hr hb) (by positivity)))
  have hC : 0<C := by dsimp only [C]; positivity
  refine ⟨δ,C,hδ,hC,?_⟩
  intro ω w μ hμ hμδ hω hw hwμ
  let W := ∑ i∈range N, ω i
  have hW : 0≤W := sum_nonneg fun i hi => (hω i (mem_range.mp hi)).1
  have hWμ : W≤(N : ℝ)*μ := by
    simpa only [sum_const,card_range,nsmul_eq_mul] using
      (sum_le_sum (fun i hi => (hω i (mem_range.mp hi)).2) : W≤∑ _i∈range N, μ)
  have hs : W+w≤b*μ := by dsimp only [b]; nlinarith
  have hμU : μ≤δU := hμδ.trans (min_le_left _ _)
  have hμhalf : μ≤1/(2*b) := hμδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hμr : μ≤r/b := hμδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hμε : μ≤ε/(2*b) := hμδ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hshalf : W+w≤(1/2 : ℝ) := by
    have hh := (le_div_iff₀ (by positivity : 0<2*b)).mp hμhalf
    nlinarith
  have hWr : W≤r := by have hh := (le_div_iff₀ hb).mp hμr; nlinarith
  have hWε : W<ε := by
    have hh := (le_div_iff₀ (by positivity : 0<2*b)).mp hμε
    nlinarith
  have hcube : CL*(W+w)^3≤C*μ^3 := by
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (add_nonneg hW hw) hs 3) hCL.le
    have he : (b*μ)^3=b^3*μ^3 := mul_pow _ _ _
    rw [he] at hp
    have hadd : 0≤CU*μ^3 := mul_nonneg hCU.le (pow_nonneg hμ 3)
    dsimp only [C]
    nlinarith
  refine ⟨?_,?_,?_⟩
  · apply le_iInf
    intro M
    exact (ENNReal.ofReal_le_ofReal (by linarith : sharpConstant W w-C*μ^3≤sharpConstant W w-CL*(W+w)^3)).trans
      (hlower M.method.policy M.consistent M.oneCorrection ω w μ r
        (fun i hi => (hω i (mem_range.mp hi)).1) hw hμ hshalf hWr hWε)
  · exact iInf_le _ (rfcMinimaxStrategy _)
  · have ht := worstOutputRatio_le (rfcMethod fullMemory 1) A g N r ω w μ
      (sharpConstant W w+CU*μ^3)
      (hupper r hrr ω w μ μ hμ hμU (fun i hi => (hω i hi).2) hwμ le_rfl)
    apply ht.trans (ENNReal.ofReal_le_ofReal _)
    have hc : CU≤C := by
      dsimp only [C]
      exact le_add_of_nonneg_left (mul_nonneg hCL.le (pow_nonneg hb.le 3))
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hc (pow_nonneg hμ 3))

/-- A finite genuine nonnegative risk bracket gives the ordinary real absolute error without assuming boundedness of every competing method.
Use: read the source minimax asymptotic in ordinary real numbers after proving its actual finiteness.
Article: main_krylov, thm:C, real risk normalization of the extended infimum–supremum.
Proof: the finite upper endpoint excludes infinity. Monotonicity of toReal
and its exact nonnegative embedding yield the real two-sided interval.
-/
theorem realRisk_bracket {q : ENNReal} {K e : ℝ} (hK : 0≤K) (he : 0≤e)
    (hl : ENNReal.ofReal (K-e)≤q) (hu : q≤ENNReal.ofReal (K+e)) :
    q≠⊤ ∧ |q.toReal-K|≤e := by
  have hfinite : q≠⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  have hlo := (ENNReal.ofReal_le_iff_le_toReal hfinite).mp hl
  have hhi : q.toReal≤K+e := by
    simpa only [ENNReal.toReal_ofReal (add_nonneg hK he)] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  exact ⟨hfinite,abs_le.mpr ⟨by linarith,by linarith⟩⟩

/-- Both the actual unknown-base minimax value and the actual RFC worst source risk equal the sharp coefficient up to the same uniform real cubic error.
Use: the displayed source asymptotic holds for the true finite-output infimum–supremum, with RFC attaining its sharp leading term.
Article: main_krylov, thm:C, complete real all-profile minimax estimate and RFC attainment.
Proof: the genuine extended source risks satisfy the proved sharp bracket.
Its upper endpoint proves actual finiteness; exact real normalization then
gives both cubic absolute-error bounds on the same source radius and tube.
-/
theorem oneCorrection_minimax_cubic {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1) :
    ∃ r₀ : ℝ, 0<r₀ ∧ ∀ r : ℝ, 0<r → r≤r₀ →
      ∃ δ C : ℝ, 0<δ ∧ 0<C ∧ ∀ (ω : ℕ → ℝ) (w μ : ℝ),
        0≤μ → μ≤δ → (∀ i<N, 0≤ω i ∧ ω i≤μ) → 0≤w → w≤μ →
        oneCorrectionMinimax A g N r ω w μ≠⊤ ∧
        worstOutputRatio (rfcMethod fullMemory 1) A g N r ω w μ≠⊤ ∧
        |(oneCorrectionMinimax A g N r ω w μ).toReal-sharpConstant (∑ i∈range N, ω i) w|≤C*μ^3 ∧
        |(worstOutputRatio (rfcMethod fullMemory 1) A g N r ω w μ).toReal-
          sharpConstant (∑ i∈range N, ω i) w|≤C*μ^3 := by
  -- The same genuine bracket controls both actual source quantities, with no methodwise boundedness assumption.
  obtain ⟨r₀,hr₀,hbracket⟩ := oneCorrection_minimax_bracket A hA g hN hcount
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
