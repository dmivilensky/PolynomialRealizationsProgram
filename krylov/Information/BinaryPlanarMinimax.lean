import krylov.Information.BinaryPlanarNormalizedLower
import krylov.Information.BinaryPlanarRFCUpper
import krylov.Information.MinimaxValue

/-!
Article: main_krylov, thm:H, the genuine gradient-only planar minimax bounds.
Use: take the actual supremum over the complete compatible binary tensor
ball and every independent unknown base coefficient, then the infimum over
the original nonanticipating stored-span CG-consistent one-query class.
Source: the proved own-base two-witness information lower bound and the
proved RFC bound on every member of that same full source family.
-/
namespace krylov.Information
noncomputable section
open Real Matrix Finset krylov.Tensor krylov.Tensor.BinaryCubic krylov.Secant
  krylov.Reference krylov.LinearAlgebra krylov.Correction krylov.Methods
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ}

/-- The actual full planar compatible-binary worst risk, retaining the independent unknown base.
Article: main_krylov, thm:H, the source planar supremum. -/
def binaryPlanarWorst (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1))))
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (g : EuclideanSpace ℝ (Fin (N+1)))
    (κ r e_c : ℝ) : ENNReal :=
  ⨆ p : {p : BinaryCubic × ℝ // p.1.InBall ∧ |p.2|≤e_c},
    ENNReal.ofReal (((binaryPlanarScenario (canonicalCGUnitStep A g 0)
      (canonicalCGUnitStep A g N) κ r p.val.2 N p.val.1).inPhysical
        (metricRoot A)⁻¹).outputRatio m g N)

/-- The actual gradient-only planar source minimax value over genuine original policies.
Article: main_krylov, thm:H, the original planar infimum of source suprema. -/
def binaryPlanarMinimax (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)
    (g : EuclideanSpace ℝ (Fin (N+1))) (κ r e_c : ℝ) : ENNReal :=
  ⨅ M : OneCorrectionCGStrategy (EuclideanSpace ℝ (Fin (N+1))),
    binaryPlanarWorst M.method.policy A g κ r e_c

/-- Every actual source method has the printed planar lower coefficient in its full compatible-source supremum.
Article: main_krylov, thm:H, uniform original-class worst-risk lower bound. -/
theorem binaryPlanarWorst_lower
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1) (r : ℝ) (hr : 0≤r) :
    ∃ ε C : ℝ, 0<ε ∧ 0<C ∧ ∀ κ e_c : ℝ, 0≤κ → κ≤e_c → e_c<ε →
      ∀ m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1))), CGConsistent m → OneCorrectionMethod m →
        ENNReal.ofReal ((κ^2/(2*(1+r)^2))*(1-C*e_c))≤binaryPlanarWorst m A g κ r e_c := by
  obtain ⟨ε,C,hε,hC,hbound⟩ := binaryPlanar_normalized_lower A hA g hN hcount r hr
  refine ⟨ε,C,hε,hC,?_⟩
  intro κ e_c hκ hκe hec m hm h1
  apply (ENNReal.ofReal_le_ofReal (hbound κ e_c hκ hκe hec m hm h1)).trans
  rw [ENNReal.ofReal_max]
  apply max_le
  · let p : {p : BinaryCubic × ℝ // p.1.InBall ∧ |p.2|≤e_c} :=
      ⟨(gradientWitness r 1,-κ*((gradientWitness r 1).t2+r*(gradientWitness r 1).t3)),
        gradientWitness_inBall hr (by norm_num),by
          rw [gradientWitness_hidden r 1 κ]
          exact gradientWitness_base_bound hr (by norm_num) hκ hκe⟩
    exact le_iSup_of_le p le_rfl
  · let p : {p : BinaryCubic × ℝ // p.1.InBall ∧ |p.2|≤e_c} :=
      ⟨(gradientWitness r (-1),-κ*((gradientWitness r (-1)).t2+r*(gradientWitness r (-1)).t3)),
        gradientWitness_inBall hr (by norm_num),by
          rw [gradientWitness_hidden r (-1) κ]
          exact gradientWitness_base_bound hr (by norm_num) hκ hκe⟩
    exact le_iSup_of_le p le_rfl

/-- Genuine full-memory RFC has the printed upper coefficient on the full planar source supremum.
Article: main_krylov, thm:H, all-compatible-tensor RFC upper bound. -/
theorem binaryPlanarWorst_rfc_upper
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1) (r : ℝ) (hr : 0≤r) :
    ∃ ε C : ℝ, 0<ε ∧ 0<C ∧ ∀ κ e_c : ℝ, 0≤κ → κ≤e_c → e_c<ε →
      binaryPlanarWorst (rfcMethod fullMemory 1) A g κ r e_c≤
        ENNReal.ofReal ((κ^2/2)*(1+r)*(1+3*r)*(1+C*e_c)) := by
  obtain ⟨ε,C,hε,hC,hbound⟩ := binaryPlanar_rfc_upper A hA g hN hcount r hr
  refine ⟨ε,C,hε,hC,?_⟩
  intro κ e_c hκ hκe hec
  apply iSup_le
  intro p
  exact ENNReal.ofReal_le_ofReal (hbound κ e_c p.val.2 hκ hκe hec p.property.2 p.val.1 p.property.1)

/-- The genuine original gradient-only planar minimax value lies between the two printed coefficients, with uniform relative linear losses.
Article: main_krylov, thm:H, both planar minimax comparisons in their actual source scope.
Every competing stored-span policy is included in the infimum, and the
upper comparison is witnessed by the genuinely executed full-memory RFC. -/
theorem binaryPlanarMinimax_bounds
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1) (r : ℝ) (hr : 0≤r) :
    ∃ ε C : ℝ, 0<ε ∧ 0<C ∧ ∀ κ e_c : ℝ, 0≤κ → κ≤e_c → e_c<ε →
      ENNReal.ofReal ((κ^2/(2*(1+r)^2))*(1-C*e_c))≤binaryPlanarMinimax A g κ r e_c ∧
      binaryPlanarMinimax A g κ r e_c≤
        ENNReal.ofReal ((κ^2/2)*(1+r)*(1+3*r)*(1+C*e_c)) := by
  obtain ⟨ε₁,C₁,hε₁,hC₁,hlower⟩ := binaryPlanarWorst_lower A hA g hN hcount r hr
  obtain ⟨ε₂,C₂,hε₂,hC₂,hupper⟩ := binaryPlanarWorst_rfc_upper A hA g hN hcount r hr
  refine ⟨min ε₁ ε₂,C₁+C₂,lt_min hε₁ hε₂,by positivity,?_⟩
  intro κ e_c hκ hκe hec
  have hec₀ := hκ.trans hκe
  constructor
  · apply le_iInf
    intro M
    apply (ENNReal.ofReal_le_ofReal ?_).trans
      (hlower κ e_c hκ hκe (hec.trans_le (min_le_left _ _)) M.method.policy M.consistent M.oneCorrection)
    have hh := mul_nonneg hC₂.le hec₀
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0≤κ^2/(2*(1+r)^2))
    nlinarith
  · apply (iInf_le_of_le (rfcMinimaxStrategy (EuclideanSpace ℝ (Fin (N+1)))) le_rfl).trans
    apply (hupper κ e_c hκ hκe (hec.trans_le (min_le_right _ _))).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0≤(κ^2/2)*(1+r)*(1+3*r))
    nlinarith [mul_nonneg hC₁.le hec₀]

end
end krylov.Information
