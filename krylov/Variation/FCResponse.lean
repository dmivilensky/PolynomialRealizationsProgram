import krylov.Variation.FCFirstVariation
import krylov.Variation.ResponseCoordinates

/-!
Article: main_krylov, thm:A, actual adaptive FC derivative equals the sharp spatial response.
Use: connect the genuine executed FC trajectory to the previously proved
attained spectral and Hilbert--Schmidt response norms on actual CG flags.
Source: differentiated actual staircase, true metric pairing and full CG basis uniqueness.
-/

namespace krylov.Variation
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped InnerProductSpace BigOperators
variable {n : ℕ}

/-- The true physical derivative of segment k induced by canonical increment derivatives.
Use: encode exactly A_k=A+Σ_(l<k)A^(1/2)E_lA^(1/2) at first order.
Article: main_krylov, thm:A, canonical perturbation convention. -/
def cumulativeDrift (base : Matrix (Fin n) (Fin n) ℝ) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base*(∑ l∈range k, E l)*metricRoot base)

/-- Two true cumulative physical derivatives differ by exactly the intervening canonical increments.
Use: the differentiated staircase is the finite triangular sum of the source canonical increments.
Article: main_krylov, thm:A, A_j−A_i.
Proof: linearity of the true physical root congruence and finite prefix telescoping. -/
theorem cumulativeDrift_sub (base : Matrix (Fin n) (Fin n) ℝ) (E : ℕ → Matrix (Fin n) (Fin n) ℝ)
    {i j : ℕ} (hij : i≤j) : cumulativeDrift base E j-cumulativeDrift base E i=
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base*(∑ l∈Ico i j, E l)*metricRoot base) := by
  unfold cumulativeDrift
  rw [← map_sub,← Matrix.sub_mul,← Matrix.mul_sub,← sum_Ico_eq_sub E hij]

/-- The genuine positive-root congruence preserves the actual physical/canonical perturbation pairing.
Use: response coordinate equations are transformed without introducing an arbitrary canonical frame or metric.
Article: main_krylov, thm:A, sᵀA^(1/2)EA^(1/2)t=σᵀEτ.
Proof: the actual root is symmetric; transfer its left factor across the
real inner product and combine the true continuous operator products. -/
theorem metric_drift_pairing (base C : Matrix (Fin n) (Fin n) ℝ)
    (s t : EuclideanSpace ℝ (Fin n)) :
    inner ℝ s (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base*C*metricRoot base) t)=
      inner ℝ (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base) s)
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C
          (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base) t)) := by
  -- Use the actual root symmetry, then identify its linear and continuous operator actions explicitly.
  have hs : (Matrix.toEuclideanLin (metricRoot base)).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr (metricRoot_isSymm base))
  have he := hs s (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base) t))
  change inner ℝ (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base) s)
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base) t))=
    inner ℝ s (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) C
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base) t))) at he
  simpa only [map_mul,mul_apply_eq_comp] using he.symm

/-- The derivative of the actually executed full-memory adaptive FC terminal canonical gradient is exactly the sharp CG flag/tail response.
Use: the previously proved sharp spectral and joint Hilbert--Schmidt constants now apply to the real FC first variation.
Article: main_krylov, thm:A, Dĝ_n[E]=ΣP_lE_lv_l.
Proof: differentiate the real FC staircase on its proved open domain. The
genuine metric congruence turns its exact coordinates into those of the constructed spatial response, and the actual full canonical CG frame separates vectors. -/
theorem fullFC_response_hasDerivAt (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : referenceAtomCount base hb g=n)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (A : ℝ → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hA : ∀ k, AnalyticAt ℝ (fun t => A t k) 0)
    (hD : ∀ k, HasDerivAt (fun t => A t k) (cumulativeDrift base E k) 0)
    (hsym : ∀ t k, (A t k).toLinearMap.IsSymmetric) (hA0 : A 0=fun _ => cgOperator base) :
    HasDerivAt (fun t => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹
      (fcGradient fullMemory (A t) g n)) (fullCycleResponse base g (range n) E) 0 := by
  -- Primitive operator derivatives are the actual canonical increment inputs; no response identity is assumed.
  obtain ⟨hQ,hpos⟩ := cgOperator_positive base hb
  have hpre := cg_nonstagnation_of_full_atoms base hb g hcount
  let G := fun t => fcGradient fullMemory (A t) g n
  have hG : HasDerivAt G (deriv G 0) 0 :=
    (quadraticFC_prefix_analytic A (fun _ => g) 0 hA analyticAt_const (cgOperator base) hA0 hQ hpos n hpre).1.differentiableAt.hasDerivAt
  have he : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹ (deriv G 0)=
      fullCycleResponse base g (range n) E := by
    apply canonical_step_inner_ext base hb g hcount
    intro i hi
    have hc := fullFC_firstVariation_coordinates A (cumulativeDrift base E) g hA hD hsym
      (cgOperator base) hA0 hQ hpos n hpre (by simpa only [hcount] using cg_terminates base hb g) hi
    rw [canonical_search_pairing base hb] at hc
    change inner ℝ (canonicalCGStep base g i)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹ (deriv G 0))=_ at hc
    rw [fullCycleResponse_coordinates base hb g hcount E hi]
    refine hc.trans (sum_congr rfl (fun j hj => ?_))
    rw [cumulativeDrift_sub base E (by have := mem_Ico.mp hj; omega)]
    exact metric_drift_pairing base _ _ _
  rw [← he]
  exact (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹).hasFDerivAt.comp_hasDerivAt 0 hG

/-- The actual affine segment sequence produced by the source canonical increment family.
Use: the sharp FC response is instantiated without assumed operator-path regularity or measured derivative fields.
Article: main_krylov, thm:A, A_k(t)=A+tA^(1/2)(Σ_(l<k)E_l)A^(1/2). -/
def canonicalFCPath (base : Matrix (Fin n) (Fin n) ℝ) (E : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (t : ℝ) (k : ℕ) : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  cgOperator base+t • cumulativeDrift base E k

/-- The actual canonical affine segment sequence is exactly the true static quadratic sequence at zero perturbation.
Use: discharge the primitive reference-value premise of the real FC response theorem.
Article: main_krylov, thm:A, A_k(0)=A.
Proof: the actual zero scalar perturbation vanishes on every physical vector. -/
theorem canonicalFCPath_zero (base : Matrix (Fin n) (Fin n) ℝ) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) :
    canonicalFCPath base E 0=fun _ => cgOperator base := by
  funext k
  apply ContinuousLinearMap.ext
  intro v
  change cgOperator base v+(0 : ℝ) • cumulativeDrift base E k v=cgOperator base v
  rw [_root_.zero_smul,_root_.add_zero]

/-- The actual canonical affine segment path is analytic and has precisely its constructed cumulative physical derivative.
Use: discharges every primitive path regularity/derivative premise in the actual FC response theorem.
Article: main_krylov, thm:A, real canonical perturbation path.
Proof: the actual path is a constant plus the parameter times its fixed cumulative physical increment. -/
theorem canonicalFCPath_calculus (base : Matrix (Fin n) (Fin n) ℝ) (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    AnalyticAt ℝ (fun t => canonicalFCPath base E t k) 0 ∧
      HasDerivAt (fun t => canonicalFCPath base E t k) (cumulativeDrift base E k) 0 := by
  constructor
  · exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  · simpa only [canonicalFCPath,one_smul,id_eq] using
      ((hasDerivAt_id (0 : ℝ)).smul_const (cumulativeDrift base E k)).const_add (cgOperator base)

/-- Symmetric source increments give a genuinely symmetric actual canonical FC segment path.
Use: every actual perturbation in the sharp derivative theorem is an admissible symmetric operator sequence.
Article: main_krylov, thm:A, symmetric physical perturbations.
Proof: finite sums preserve Hermitian symmetry, and congruence by the actual
symmetric positive root preserves it; actual real scalar multiplication and addition preserve physical operator symmetry. -/
theorem canonicalFCPath_symmetric (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l, (E l).IsSymm) (t : ℝ) (k : ℕ) :
    (canonicalFCPath base E t k).toLinearMap.IsSymmetric := by
  -- The cumulative derivative is a genuine root congruence of the actual symmetric increment sum.
  have hsum : (∑ l∈range k, E l).IsHermitian := by
    change (∑ l∈range k, E l)ᴴ=∑ l∈range k, E l
    rw [conjTranspose_sum]
    exact sum_congr rfl (fun l _ => (Matrix.isHermitian_iff_isSymm.mpr (hE l)).eq)
  have hroot : (metricRoot base).IsHermitian := Matrix.isHermitian_iff_isSymm.mpr (metricRoot_isSymm base)
  have hc := Matrix.isHermitian_conjTranspose_mul_mul (metricRoot base) hsum
  rw [hroot.eq] at hc
  have hC : (cumulativeDrift base E k).toLinearMap.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hc
  change ((cgOperator base).toLinearMap+t • (cumulativeDrift base E k).toLinearMap).IsSymmetric
  exact (cgOperator_positive base hb).1.add (LinearMap.IsSymmetric.smul (by rfl) hC)

/-- The actual FC terminal derivative along the source's constructed canonical segment perturbation is its sharp spatial CG response.
Use: a complete algorithm-level first-variation theorem with all primitive path hypotheses discharged.
Article: main_krylov, thm:A, actual canonical perturbation realization.
Proof: the constructed affine path has its proved actual derivative, analyticity,
symmetry and exact reference value, so the proved real adaptive FC response theorem applies. -/
theorem canonicalFC_response_hasDerivAt (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hcount : referenceAtomCount base hb g=n)
    (E : ℕ → Matrix (Fin n) (Fin n) ℝ) (hE : ∀ l, (E l).IsSymm) :
    HasDerivAt (fun t => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base)⁻¹
      (fcGradient fullMemory (canonicalFCPath base E t) g n)) (fullCycleResponse base g (range n) E) 0 :=
  fullFC_response_hasDerivAt base hb g hcount E (canonicalFCPath base E)
    (fun k => (canonicalFCPath_calculus base E k).1) (fun k => (canonicalFCPath_calculus base E k).2)
    (canonicalFCPath_symmetric base hb E hE) (canonicalFCPath_zero base E)

end
end krylov.Variation
