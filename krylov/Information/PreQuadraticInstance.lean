import krylov.Information.InstanceOwnMetric
import krylov.Information.ReferenceErrorBall

/-!
Article: main_krylov, s4:cor-Q, full original pre-quadratic instance inequality.
Use: choose one genuine fixed-reference radius and relative error constant
before every original profile, physical scenario and competing method.
Source: actual common admissible twin, genuine centred RFC execution,
original-budget robust radius and proved compact true CG normalization.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator MatrixOrder
variable {N : ℕ}

/-- The original pre-quadratic inner source class satisfies the printed actual own-normalized instance inequality for every genuine one-correction CG-consistent method.
Use: Discharge actual centre-domain, reflected-source and reference-normalization premises with the original source hypotheses.
Article: main_krylov, s4:cor-Q, original instance-optimality and inner attainment.
Proof: Choose the genuine compact reference ball first. Primitive inner slack gives the actual common admissible twin and its true base displacement. Exact physical metric comparison and the proved common relative CG-error bound yield the printed three losses and the precise constant n(6+4(1+r)L). -/
theorem preQuadratic_instance
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hcountA : referenceAtomCount A hA g=N+1) (hN : 0<N) :
    ∃ r₀ L : ℝ, 0<r₀ ∧ r₀<1 ∧ 0≤L ∧ ∀ (r : ℝ), 0≤r → r≤r₀ →
      ∀ (ω : ℕ → ℝ) (w τ μ : ℝ), 0≤w → 0≤τ → 0≤μ →
        (∀ i<N, ω i≤μ) → w≤μ →
        4*((N : ℝ)+1)*(∑ i∈range N, ω i)≤1 → 6*((N : ℝ)+1)*μ≤1 →
      ∀ S : Scenario (N+1), S.NaturalInner A r ω w τ →
      ∀ (Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hQ : Q.PosDef),
        referenceAtomCount Q hQ g=N+1 → S.PreQuadratic (cgOperator Q) g N →
      ∀ m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1))), CGConsistent m → OneCorrectionMethod m →
        (1-((N : ℝ)+1)*(6+4*(1+r)*L)*μ)*S.outputRatio (rfcMethod fullMemory 1) g N≤
          max (S.outputRatio m g N) ((S.preQuadraticTwin Q g).outputRatio m g N) := by
  -- The true compact reference ball and relative normalization constant precede every source and method.
  obtain ⟨r₀,L,hr₀,hr₁,hL,hcontrol⟩ := referenceBaseChart_relative_error_ball A hA g hcountA
  refine ⟨r₀,L,hr₀,hr₁,hL,?_⟩
  intro r hr hrr ω w τ μ hw hτ hμ hω hwμ hsmall hμsmall S h Q hQ hcountQ hpre m hm h1
  let T := S.preQuadraticTwin Q g
  let W := ∑ i∈range N, ω i
  have hW : 0≤W := sum_nonneg fun i hi =>
    (norm_nonneg (relativeOperator S.base (S.increment i))).trans (h.original.2.2.1 i (mem_range.mp hi)).2
  have hT := h.commonTwin_admissible hA hQ hcountQ hpre hN hr hw hτ hsmall
  have hd := h.commonTwin_base_displacement hA hQ hcountQ hpre hN hr hw hsmall
  have hbase : S.base≤(1+r) • A :=
    (relative_displacement_base A S.base hA h.original.1.1.isSymm hr (hrr.trans_lt hr₁) h.original.2.1).2.1
  have hsym : (T.base-S.base).IsSymm := hT.1.1.isSymm.sub h.original.1.1.isSymm
  have hmove : relativeBudget A (T.base-S.base)≤4*(1+r)*W := by
    have he := relative_budget_upper_metric A S.base (T.base-S.base) hA h.original.1 hsym
      (by linarith : 0≤1+r) (by positivity : 0≤4*W) hbase hd
    nlinarith [he]
  have hφ := hcontrol S.base T.base h.original.1 hT.1 (h.original.2.1.trans hrr) (hT.2.1.trans hrr)
  have herror : ‖cgCanonicalError T.base g N‖≤‖cgCanonicalError S.base g N‖*(1+4*(1+r)*L*W) := by
    calc
      _ ≤ ‖cgCanonicalError S.base g N‖*(1+L*relativeBudget A (T.base-S.base)) := hφ.2.2
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_left hmove hL]) (norm_nonneg _)
  exact h.instance_of_normalization hA hQ hcountQ hpre hN hr hw hτ hμ hL hω hwμ hsmall hμsmall
    hφ.1 hφ.2.1 herror m hm h1

end
end krylov.Information
