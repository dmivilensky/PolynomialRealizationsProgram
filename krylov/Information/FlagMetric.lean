import krylov.Information.MetricSlack
import krylov.Information.PhysicalCentre

/-!
Article: main_krylov, thm:centre, quantitative bounds for the method's own flag.
Use: derive the distortion of every prefix, complementary projection and
reflection from the actual energy-normalized direction Gram matrix.
Source: the symmetric spectral norm/Loewner equivalence, diagonal congruence
and the exact change-of-base lemma; no projector bound is an extra premise.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Secant
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
variable {p : ℕ}

/-- The actual positive energy scale of each direction-coordinate axis.
Use: normalize the Gram matrix without choosing a spectral basis.
Article: main_krylov, apD:centre, N=diag(‖d_i‖_(A₀)). -/
def directionScale (G : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  diagonal fun i => Real.sqrt (G i i)

/-- The Gram matrix of the actual energy-normalized directions.
Use: its distance from the identity measures the method's own near conjugacy.
Article: main_krylov, apD:centre, ΣᵀΣ. -/
def normalizedDirectionGram (G : Matrix (Fin p) (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  (directionScale G)⁻¹ * G * (directionScale G)⁻¹

/-- The actual normalized Gram defect, using the fixed spectral norm convention.
Use: the quantitative flag bounds include zero defects and zero-dimensional matrices.
Article: main_krylov, apD:centre, ε=‖ΣᵀΣ−I‖. -/
def directionDefect (G : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  chebyshev1.opNorm (normalizedDirectionGram G-1)

/-- The squared condition bound associated with the actual Gram defect.
Use: one common constant controls all old and hidden flag compressions.
Article: main_krylov, apD:centre, κ_ε²=(1+ε)/(1−ε). -/
def flagDistortion (G : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  (1+directionDefect G)/(1-directionDefect G)

/-- Positive coordinate energy makes the actual diagonal normalization invertible.
Use: cancel the normalization in the physical metric sandwich.
Article: main_krylov, apD:centre, invertibility of N.
Proof: all diagonal square roots are strictly positive, hence their determinant product is nonzero. -/
theorem directionScale_unit (G : Matrix (Fin p) (Fin p) ℝ) (hG : G.PosDef) :
    IsUnit (directionScale G).det := by
  rw [directionScale,det_diagonal,isUnit_iff_ne_zero]
  exact prod_ne_zero_iff.mpr fun i _ => (Real.sqrt_pos.mpr (hG.diag_pos (i := i))).ne'

/-- Squaring the genuine direction-energy scale gives the diagonal energy form.
Use: the reference diagonal in the Loewner sandwich has no independent normalization.
Article: main_krylov, apD:centre, N²=diag(DᵀA₀D).
Proof: square each positive diagonal square root. -/
theorem directionScale_square (G : Matrix (Fin p) (Fin p) ℝ) (hG : G.PosDef) :
    directionScale G * directionScale G=diagonal (fun i => G i i) := by
  simp only [directionScale,diagonal_mul_diagonal]
  congr 1
  ext i
  exact Real.mul_self_sqrt (hG.diag_pos (i := i)).le

/-- The normalized coordinate Gram is exactly the Gram of the physical normalized directions.
Use: the defect used below is the article's actual ΣᵀΣ, including arbitrary oblique directions.
Article: main_krylov, apD:centre, Σ=A₀¹ᐟ²DN⁻¹.
Proof: transpose the actual product and square its genuine positive metric root. -/
theorem normalizedDirectionGram_physical (A D : Matrix (Fin p) (Fin p) ℝ)
    (hA : A.PosDef) :
    let G := Dᵀ*A*D
    let V := metricRoot A*D*(directionScale G)⁻¹
    normalizedDirectionGram G=Vᵀ*V := by
  -- The physical Gram uses the same actual direction-energy diagonal as its coordinate normalization.
  dsimp only
  simp only [normalizedDirectionGram,transpose_mul,transpose_nonsing_inv,
    directionScale,diagonal_transpose,(metricRoot_isSymm A).eq]
  symm
  calc
    _ = (diagonal fun i => Real.sqrt ((Dᵀ*A*D) i i))⁻¹ *
        (Dᵀ*(metricRoot A*metricRoot A)*D) *
        (diagonal fun i => Real.sqrt ((Dᵀ*A*D) i i))⁻¹ := by noncomm_ring
    _ = _ := by rw [metricRoot_square A hA]

/-- Actual near conjugacy yields the exact diagonal energy sandwich.
Use: derive all quantitative oblique flag bounds from the observed direction geometry.
Article: main_krylov, thm:centre(iii), (1−ε)N²≼DᵀA₀D≼(1+ε)N².
Proof: bound the symmetric normalized Gram defect by its actual spectral norm,
then undo the genuine diagonal normalization by congruence. -/
theorem directionGram_sandwich (G : Matrix (Fin p) (Fin p) ℝ) (hG : G.PosDef) :
    (1-directionDefect G) • diagonal (fun i => G i i) ≤ G ∧
      G ≤ (1+directionDefect G) • diagonal (fun i => G i i) := by
  -- First prove both endpoints in normalized coordinates, then cancel the energy scales.
  let N := directionScale G
  let M := normalizedDirectionGram G
  have hN : (directionScale G).IsSymm := isSymm_diagonal _
  have hM : (M-1).IsHermitian := Matrix.isHermitian_iff_isSymm.mpr (by
    simp only [M,normalizedDirectionGram,Matrix.IsSymm,transpose_sub,transpose_mul,
      transpose_nonsing_inv,hN.eq,hG.1.isSymm.eq,transpose_one,Matrix.mul_assoc])
  have hn : 0 ≤ directionDefect G := chebyshev1.opNorm_nonneg _
  obtain ⟨hu,hl⟩ := (krylov.LinearAlgebra.spectral_norm_iff_shifted_posSemidef
    (M-1) hM hn).mp (le_refl (directionDefect G))
  have hl' : (1-directionDefect G) • (1 : Matrix (Fin p) (Fin p) ℝ) ≤ M := by
    rw [Matrix.le_iff]
    convert hl using 1; module
  have hu' : M ≤ (1+directionDefect G) • (1 : Matrix (Fin p) (Fin p) ℝ) := by
    rw [Matrix.le_iff]
    convert hu using 1; module
  have he : N*M*N=G := by
    simp only [N,M,normalizedDirectionGram,← Matrix.mul_assoc]
    rw [mul_nonsing_inv _ (directionScale_unit G hG),Matrix.one_mul,
      Matrix.mul_assoc,nonsing_inv_mul _ (directionScale_unit G hG),Matrix.mul_one]
  have hh := And.intro (congruence_mono hl' N) (congruence_mono hu' N)
  have hNt : Nᵀ=N := hN.eq
  simpa only [hNt,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,he,
    show N*N=diagonal (fun i => G i i) from directionScale_square G hG] using hh

/-- A coordinate contraction decreases every nonnegative diagonal energy form.
Use: one result covers the old prefix, hidden complement and sign reflection.
Article: main_krylov, thm:centre(iii), PᵀN²P≼N².
Proof: the diagonal difference has entries c_i(1−a_i²), all nonnegative. -/
theorem diagonal_energy_contraction (c a : Fin p → ℝ) (hc : ∀ i, 0 ≤ c i)
    (ha : ∀ i, |a i| ≤ 1) :
    (diagonal a)ᵀ*diagonal c*diagonal a ≤ diagonal c := by
  rw [diagonal_transpose,diagonal_mul_diagonal,diagonal_mul_diagonal,Matrix.le_iff,
    diagonal_sub,posSemidef_diagonal_iff]
  intro i
  have hsq : a i*a i ≤ 1 := by nlinarith [abs_le.mp (ha i)]
  nlinarith [mul_nonneg (hc i) (sub_nonneg.mpr hsq)]

/-- The exact near-conjugacy constant controls every coordinate-contraction pullback of the metric.
Use: obtain all actual oblique projector and reflection distortion bounds together.
Article: main_krylov, thm:centre(iii), Pᵀ(DᵀA₀D)P≼κ_ε²DᵀA₀D.
Proof: contract the diagonal energy upper bound and use its strictly positive
lower bound; the ratio of the two endpoints is exactly κ_ε². -/
theorem flag_metric_domination (G : Matrix (Fin p) (Fin p) ℝ) (hG : G.PosDef)
    (he : directionDefect G < 1) (a : Fin p → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    (diagonal a)ᵀ*G*diagonal a ≤ flagDistortion G • G := by
  -- The diagonal form contracts before comparing it back with the actual oblique metric.
  obtain ⟨hl,hu⟩ := directionGram_sandwich G hG
  have hn : 0 ≤ directionDefect G := chebyshev1.opNorm_nonneg _
  have hk : 0 ≤ flagDistortion G := div_nonneg (by linarith) (by linarith)
  have hc := diagonal_energy_contraction (fun i => G i i) a
    (fun i => (hG.diag_pos (i := i)).le) ha
  have hscale := smul_le_smul_of_nonneg_left hl hk
  have hr : flagDistortion G*(1-directionDefect G)=1+directionDefect G := by
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr (ne_of_gt he))
  rw [smul_smul,hr] at hscale
  calc
    _ ≤ (diagonal a)ᵀ*((1+directionDefect G) • diagonal (fun i => G i i))*diagonal a :=
      congruence_mono hu _
    _ ≤ (1+directionDefect G) • diagonal (fun i => G i i) := by
      simpa only [Matrix.mul_smul,Matrix.smul_mul] using
        smul_le_smul_of_nonneg_left hc (by linarith : 0 ≤ 1+directionDefect G)
    _ ≤ flagDistortion G • G := hscale

/-- Symmetric coordinate contractions cost at most the exact near-conjugacy factor in relative budget.
Use: admissibility of every reflected increment and hidden-block displacement.
Article: main_krylov, thm:centre(iii), ‖PᵀEP‖_G≤κ_ε²‖E‖_G.
Proof: congruence of both signed spectral-budget inequalities is bounded by
the proved metric domination, then converted back to the actual relative norm. -/
theorem flag_relative_budget (G E : Matrix (Fin p) (Fin p) ℝ)
    (hG : G.PosDef) (hE : E.IsSymm) (he : directionDefect G < 1)
    (a : Fin p → ℝ) (ha : ∀ i, |a i| ≤ 1) :
    relativeBudget G ((diagonal a)ᵀ*E*diagonal a) ≤
      flagDistortion G*relativeBudget G E := by
  -- Control the two signed congruences using the same actual positive metric bound.
  have hw : 0 ≤ relativeBudget G E := chebyshev1.opNorm_nonneg _
  have hk : 0 ≤ flagDistortion G := div_nonneg
    (by have hn : 0 ≤ directionDefect G := chebyshev1.opNorm_nonneg _; linarith)
    (by linarith)
  obtain ⟨hl,hu⟩ := (relative_norm_le_iff G E hG hE hw).mp le_rfl
  have hs := smul_le_smul_of_nonneg_left (flag_metric_domination G hG he a ha) hw
  have hsym : ((diagonal a)ᵀ*E*diagonal a).IsSymm := by
    simp only [Matrix.IsSymm,transpose_mul,transpose_transpose,hE.eq,Matrix.mul_assoc]
  apply (relative_norm_le_iff _ _ hG hsym (mul_nonneg hk hw)).mpr
  rw [smul_smul,mul_comm (relativeBudget G E)] at hs
  constructor
  · exact (neg_le_neg hs).trans (by
      simpa only [Matrix.mul_neg,Matrix.neg_mul,Matrix.mul_smul,Matrix.smul_mul]
        using congruence_mono hl (diagonal a))
  · have hu' := congruence_mono hu (diagonal a)
    simp only [Matrix.mul_smul,Matrix.smul_mul] at hu'
    exact hu'.trans hs

end
end krylov.Information
