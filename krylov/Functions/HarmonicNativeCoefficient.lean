import krylov.Tensor.HarmonicEndpointResponse

/-!
Article: main_krylov, thm:H, the exact native harmonic cubic coefficient.
Use: identify the genuine physical function's native RFC coefficient with
the explicitly evaluated endpoint harmonic response and its Euclidean norm.
Source: true physical/canonical cubic transport and original finite CG sums.
-/

namespace krylov.Functions
noncomputable section
open Matrix Finset krylov.Tensor krylov.Reference krylov.Variation krylov.Correction
  krylov.Envelope krylov.Nonlinear
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n k : ℕ}

/-- The actual fresh vector depends only on its original preterminal increments.
Article: main_krylov, thm:H. -/
theorem harmonic_fresh_prefix_congr (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (E E' : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hE : ∀ l∈range (N-1), E l=E' l) :
    freshDefect base g E N=freshDefect base g E' N := by
  unfold freshDefect
  apply sum_congr rfl
  intro l hl
  rw [hE l hl]

/-- The actual staircase depends only on its original preterminal increments.
Article: main_krylov, thm:H. -/
theorem harmonic_staircase_prefix_congr (base : Matrix (Fin n) (Fin n) ℝ)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ)
    (E E' : ℕ → Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (hE : ∀ l∈range (N-1), E l=E' l) :
    staircaseOperator base g E F N=staircaseOperator base g E' F N := by
  unfold staircaseOperator
  congr 1
  apply sum_congr rfl
  intro l hl
  rw [hE l hl]

/-- The genuine native RFC coefficient for the actual harmonic scalar
function is exactly its original endpoint harmonic product.
Article: main_krylov, thm:H. -/
theorem rfc_harmonic_coefficient_endpoint
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (u : EuclideanSpace ℝ (Fin (k+1))) (hk : 2 ≤ k) (a : ℝ)
    (hN : referenceAtomCount base hb (cgOperator base u)=k+1) :
    rfcTensorCanonicalCoefficient base hb
      (metricCubicVariation (metricCoordinates base hb)
        (referenceHarmonicTensor base hb (cgOperator base u) a)) u =
      ‖canonicalCGStep base (cgOperator base u) k‖ •
        staircaseOperator base (cgOperator base u)
          (harmonicEndpointIncrement base hb (cgOperator base u) a)
          (referenceHarmonicLastMatrix base hb (cgOperator base u) a) (k+1)
          (freshDefect base (cgOperator base u)
            (harmonicEndpointIncrement base hb (cgOperator base u) a) (k+1)) := by
  let g := cgOperator base u
  let T := referenceHarmonicTensor base hb g a
  let D := metricCubicVariation (metricCoordinates base hb) T
  have hcount : 3 ≤ referenceAtomCount base hb g := by rw [hN]; omega
  have hE : ∀ l∈range ((k+1)-1), rfcCompatibleIncrements base hb D u l =
      harmonicEndpointIncrement base hb g a l := by
    intro l hl
    have hl' : l < referenceAtomCount base hb g-1 := by rw [hN]; exact mem_range.mp hl
    rw [rfcCompatibleIncrements_metricCubic,
      reference_harmonic_increment_matrix base hb g hcount a ⟨l,hl'⟩]
    rfl
  have hF : rfcCompatibleCorrection base hb D u k=referenceHarmonicLastMatrix base hb g a := by
    rw [rfcCompatibleCorrection_metricCubic]
    convert reference_harmonic_correction_matrix base hb g (by omega : 2≤referenceAtomCount base hb g) a using 1
    rw [hN,Nat.add_sub_cancel]
  change ‖canonicalCGStep base g k‖ • staircaseOperator base g
      (rfcCompatibleIncrements base hb D u) (rfcCompatibleCorrection base hb D u k) (k+1)
      (freshDefect base g (rfcCompatibleIncrements base hb D u) (k+1)) = _
  rw [hF,harmonic_staircase_prefix_congr base g (k+1) _ _ _ hE,
    harmonic_fresh_prefix_congr base g (k+1) _ _ hE]

/-- The genuine native harmonic coefficient has exactly the article's
two-dimensional leading norm, including its true last-step energy factor.
Article: main_krylov, thm:H. -/
theorem rfc_harmonic_coefficient_norm
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (u : EuclideanSpace ℝ (Fin (k+1))) (hk : 2 ≤ k) (a : ℝ)
    (hN : referenceAtomCount base hb (cgOperator base u)=k+1) :
    let p := a*‖canonicalCGStep base (cgOperator base u) 0‖/Real.sqrt 2
    let q := a*‖canonicalCGStep base (cgOperator base u) k‖/Real.sqrt 2
    ‖rfcTensorCanonicalCoefficient base hb
      (metricCubicVariation (metricCoordinates base hb)
        (referenceHarmonicTensor base hb (cgOperator base u) a)) u‖ =
        ‖canonicalCGStep base (cgOperator base u) k‖ * |p-q| * Real.sqrt ((p+2*q)^2+q^2) := by
  dsimp only
  rw [rfc_harmonic_coefficient_endpoint base hb u hk a hN,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  have hh := harmonicEndpoint_product_norm base hb (cgOperator base u)
    (by rw [hN]; omega : 3≤referenceAtomCount base hb (cgOperator base u)) a
  rw [hN,Nat.add_sub_cancel] at hh
  rw [hh]
  ring

end
end krylov.Functions
