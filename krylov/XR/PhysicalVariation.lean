import krylov.XR.ConjugateVariation

/-!
Article: main_krylov, prop:status, original physical-window theorem.
Use: derive every compressed allowance from the original symmetric
physical increments and their correction-operator budgets; apply the
actual Hermitian test to S^T Y. Source: Loewner congruence and the exact
physical/observed flag dictionary already proved for thm:window.
-/
namespace krylov.XR
noncomputable section
open Matrix Finset krylov.Secant
open scoped Matrix.Norms.L2Operator MatrixOrder BigOperators
variable {n p : ℕ}

/-- A full-column-rank physical step window has a genuine positive
correction-base Gram matrix. Article: main_krylov, prop:status. -/
theorem physical_gram_posDef (S : Matrix (Fin n) (Fin p) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef) (hS : Function.Injective S.mulVec) :
    (Sᵀ*B*S).PosDef := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using hB.conjTranspose_mul_mul_same hS

/-- The original physical increment budget transfers to the actual Gram
metric without loss, independently of the window conditioning.
Article: main_krylov, prop:status. -/
theorem physical_compressed_budget (S : Matrix (Fin n) (Fin p) ℝ)
    (B E : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef) (hE : E.IsSymm)
    (hS : Function.Injective S.mulVec) (ω : ℝ) (hbudget : relativeBudget B E≤ω) :
    relativeBudget (Sᵀ*B*S) (Sᵀ*E*S)≤ω := by
  have hω : 0≤ω := (norm_nonneg _).trans hbudget
  have hG := physical_gram_posDef S B hB hS
  have hs : (Sᵀ*E*S).IsSymm := by
    simp only [IsSymm,transpose_mul,transpose_transpose,hE.eq,Matrix.mul_assoc]
  apply (relative_norm_le_iff _ _ hG hs hω).mpr
  have hb := (relative_norm_le_iff B E hB hE hω).mp hbudget
  have hl := congruence_mono hb.1 S
  have hu := congruence_mono hb.2 S
  simpa only [Matrix.mul_neg,Matrix.neg_mul,Matrix.mul_smul,Matrix.smul_mul] using And.intro hl hu

/-- Original physical data give both clauses of the general-window
variation certificate, with the exact actual kappa_flat and no supplied
model/test certificates. Article: main_krylov, prop:status. -/
theorem physical_window_variation_status (S : Matrix (Fin n) (Fin p) ℝ)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ k,(A k).IsSymm)
    (hB : (A p).PosDef) (hS : Function.Injective S.mulVec) (ω : ℕ → ℝ)
    (hbudget : ∀ l<p,relativeBudget (A p) (A (l+1)-A l)≤ω l)
    (θ : ℝ) (hθ : 0<θ) :
    let G := Sᵀ*A p*S
    let M := Sᵀ*pairImages S A
    ((∑ l∈range p,ω l)<θ/((2+θ)*flagCondition G^2) → windowUnrefuted θ M ∧
      relativeBudget (latest M) (G-latest M)<θ/2) ∧
    (¬windowUnrefuted θ M → θ/((2+θ)*flagCondition G^2)≤∑ l∈range p,ω l) := by
  let C := fun k=>Sᵀ*A k*S
  have hc (k : ℕ) : (C k).IsSymm := by
    simp only [C,IsSymm,transpose_mul,transpose_transpose,(hA k).eq,Matrix.mul_assoc]
  have hg : (C p).PosDef := physical_gram_posDef S (A p) hB hS
  have hw (l : ℕ) (hl : l<p) : 0≤ω l := (norm_nonneg _).trans (hbudget l hl)
  have hb (l : ℕ) (hl : l<p) : relativeBudget (C p) (C (l+1)-C l)≤ω l := by
    have hh := physical_compressed_budget S (A p) (A (l+1)-A l) hB
      ((hA _).sub (hA _)) hS (ω l) (hbudget l hl)
    simpa only [C,Matrix.mul_sub,Matrix.sub_mul] using hh
  have hr := observed_variation_retention C hc hg ω hw hb θ hθ
  have hf := observed_variation_refutation C hc hg ω hw hb θ hθ
  dsimp only
  simpa only [C,observed_compression] using And.intro hr hf

/-- True B-conjugacy gives the original sharp constant-one certificate
for the actual physical window and original increment budgets.
Article: main_krylov, prop:status. -/
theorem physical_conjugate_variation_status (S : Matrix (Fin n) (Fin p) ℝ)
    (A : ℕ → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ k,(A k).IsSymm)
    (hB : (A p).PosDef) (hS : Function.Injective S.mulVec)
    (d : Fin p → ℝ) (hdiag : Sᵀ*A p*S=diagonal d) (ω : ℕ → ℝ)
    (hbudget : ∀ l<p,relativeBudget (A p) (A (l+1)-A l)≤ω l)
    (θ : ℝ) (hθ : 0<θ) :
    let G := Sᵀ*A p*S
    let M := Sᵀ*pairImages S A
    ((∑ l∈range p,ω l)<θ/(1+θ) → windowUnrefuted θ M ∧
      relativeBudget (latest M) (G-latest M)<θ) ∧
    (¬windowUnrefuted θ M → θ/(1+θ)≤∑ l∈range p,ω l) := by
  let C := fun k=>Sᵀ*A k*S
  have hc (k : ℕ) : (C k).IsSymm := by
    simp only [C,IsSymm,transpose_mul,transpose_transpose,(hA k).eq,Matrix.mul_assoc]
  have hg : (C p).PosDef := physical_gram_posDef S (A p) hB hS
  have hw (l : ℕ) (hl : l<p) : 0≤ω l := (norm_nonneg _).trans (hbudget l hl)
  have hb (l : ℕ) (hl : l<p) : relativeBudget (C p) (C (l+1)-C l)≤ω l := by
    have hh := physical_compressed_budget S (A p) (A (l+1)-A l) hB
      ((hA _).sub (hA _)) hS (ω l) (hbudget l hl)
    simpa only [C,Matrix.mul_sub,Matrix.sub_mul] using hh
  have hh := conjugate_observed_status C hc hg d hdiag ω hw hb θ hθ
  dsimp only
  simpa only [C,observed_compression] using hh

end
end krylov.XR
