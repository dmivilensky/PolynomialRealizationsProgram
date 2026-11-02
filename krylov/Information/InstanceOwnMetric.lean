import krylov.Information.InstanceScalar
import krylov.Information.InstanceMetric
import krylov.Information.SharpMetricComparison
import krylov.Information.RelativeReferenceError

/-!
Article: main_krylov, s4:cor-Q, actual original own-normalized instance comparison.
Use: compare genuine executed outputs in their own true base metrics and
actual last-CG-error normalizations with exactly the printed source losses.
Source: original common-twin source slack, exact physical spectral metric
comparison and true compact CG reference-error regularity.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator MatrixOrder
variable {N : ℕ}

/-- The actual common admissible pre-quadratic twin satisfies the printed own-normalized instance factor once its genuine positive reference normalizations have been compared.
Use: Combine the real robust RFC radius, exact original 4W twin displacement and actual reference-error bound.
Article: main_krylov, s4:cor-Q, original source instance-optimality factor.
Proof: Derive the genuine twin admissibility and true base domination from original inner slack. The sharp actual dual-norm comparison costs 2W. Apply the proved ratio algebra to the two real executed residuals and their actual own-reference errors; W is at most n times the maximal original budget. -/
theorem Scenario.NaturalInner.instance_of_normalization {S : Scenario (N+1)}
    {A Q : Matrix (Fin (N+1)) (Fin (N+1)) ℝ} (hA : A.PosDef) (hQ : Q.PosDef)
    {g : EuclideanSpace ℝ (Fin (N+1))} (hcount : referenceAtomCount Q hQ g=N+1)
    {r w τ μ L : ℝ} {ω : ℕ → ℝ} (h : S.NaturalInner A r ω w τ)
    (hpre : S.PreQuadratic (cgOperator Q) g N) (hN : 0<N)
    (hr : 0≤r) (hw : 0≤w) (hτ : 0≤τ) (hμ : 0≤μ) (hL : 0≤L)
    (hprofile : ∀ i<N, ω i≤μ) (hwμ : w≤μ)
    (hsmall : 4*((N : ℝ)+1)*(∑ i∈range N, ω i)≤1) (hμsmall : 6*((N : ℝ)+1)*μ≤1)
    (hφ : 0<‖cgCanonicalError S.base g N‖)
    (hψ : 0<‖cgCanonicalError (S.preQuadraticTwin Q g).base g N‖)
    (herror : ‖cgCanonicalError (S.preQuadraticTwin Q g).base g N‖≤
      ‖cgCanonicalError S.base g N‖*(1+4*(1+r)*L*(∑ i∈range N, ω i)))
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (hm : CGConsistent m) (h1 : OneCorrectionMethod m) :
    (1-((N : ℝ)+1)*(6+4*(1+r)*L)*μ)*S.outputRatio (rfcMethod fullMemory 1) g N≤
      max (S.outputRatio m g N) ((S.preQuadraticTwin Q g).outputRatio m g N) := by
  -- The genuine reflected source and base displacement are derived before comparing any actual residuals.
  let T := S.preQuadraticTwin Q g
  let W := ∑ i∈range N, ω i
  have hW : 0≤W := sum_nonneg fun i hi =>
    (norm_nonneg (relativeOperator S.base (S.increment i))).trans (h.original.2.2.1 i (mem_range.mp hi)).2
  have hWμ : W≤((N : ℝ)+1)*μ := by
    calc
      _ ≤ ∑ i∈range N, μ := sum_le_sum fun i hi => hprofile i (mem_range.mp hi)
      _ = (N : ℝ)*μ := by simp
      _ ≤ _ := by nlinarith
  have hT := h.commonTwin_admissible hA hQ hcount hpre hN hr hw hτ hsmall
  have hd := h.commonTwin_base_displacement hA hQ hcount hpre hN hr hw hsmall
  have hsym : (T.base-S.base).IsSymm := hT.1.1.isSymm.sub h.original.1.1.isSymm
  have hu := ((relative_norm_le_iff S.base (T.base-S.base) h.original.1 hsym
    (by positivity : 0≤4*W)).mp hd).2
  have hbase : T.base≤(1+4*W) • S.base := by
    have he := add_le_add_left hu S.base
    convert he using 1 <;> module
  let sf := ‖cgOperator (metricRoot S.base)⁻¹ (probedGradient m S.probeOracle (S.correctionOracle N) g (N+1))‖
  let tf := ‖cgOperator (metricRoot S.base)⁻¹ (probedGradient m T.probeOracle (T.correctionOracle N) g (N+1))‖
  let ownT := ‖cgOperator (metricRoot T.base)⁻¹ (probedGradient m T.probeOracle (T.correctionOracle N) g (N+1))‖
  let f := ‖cgOperator (metricRoot S.base)⁻¹ (probedGradient (rfcMethod fullMemory 1) S.probeOracle (S.correctionOracle N) g (N+1))‖
  have hmetric : tf≤(1+2*W)*ownT := by
    simpa only [show 4*W/2=2*W by ring] using dual_norm_le_one_add_half S.base T.base h.original.1 hT.1
      (by positivity : 0≤4*W) hbase (probedGradient m T.probeOracle (T.correctionOracle N) g (N+1))
  have hradius : f≤(1+4*((N : ℝ)+1)*μ)*max sf tf :=
    hpre.rfc_instance_fixed_metric hQ hcount hN h.original.1 (fun i hi => (h.original.2.2.1 i hi).1)
      h.original.2.2.2.1 ω w μ hμ (fun i hi => (h.original.2.2.1 i hi).2) h.original.2.2.2.2.1
      hprofile hwμ hsmall hμsmall m hm h1
  have hc := instance_ratio_factor (f := f) (s := sf) (t := tf) (u := ownT)
    (φ := ‖cgCanonicalError S.base g N‖) (ψ := ‖cgCanonicalError T.base g N‖)
    (a := 4*((N : ℝ)+1)*μ) (b := 2*W) (c := 4*(1+r)*L*W)
    (norm_nonneg _) (norm_nonneg _) hφ hψ (by positivity) (by positivity) (by positivity)
    hradius hmetric herror
  change (1-(4*((N : ℝ)+1)*μ+2*W+4*(1+r)*L*W))*S.outputRatio (rfcMethod fullMemory 1) g N≤_ at hc
  have hfactor : 1-((N : ℝ)+1)*(6+4*(1+r)*L)*μ≤1-(4*((N : ℝ)+1)*μ+2*W+4*(1+r)*L*W) := by
    nlinarith [mul_le_mul_of_nonneg_left hWμ (by positivity : 0≤2+4*(1+r)*L)]
  exact (mul_le_mul_of_nonneg_right hfactor (div_nonneg (norm_nonneg _) hφ.le)).trans hc

end
end krylov.Information
