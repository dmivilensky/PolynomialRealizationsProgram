import krylov.Envelope.SelectionNuclearDual

set_option autoImplicit false
/-!
Article: main_krylov, thm:select, concrete aligned spectral-sign minimax attainers.
Use: construct the printed attaining source increments and identify
their actual common tilt with the selection value times the maximizing
unit polynomial vector, including the zero-value case.
Source: genuine nuclear support attainment and equality in real Hilbert
Cauchy--Schwarz, proved here by the squared norm of the actual difference.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.LinearAlgebra Polynomial Matrix Set
open scoped BigOperators Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- For every maximizing actual unit polynomial, its concrete feasible spectral-sign scenario has genuine common tilt equal to the selection value times that true unit polynomial vector.
Use: For every maximizing actual unit polynomial, its concrete feasible spectral-sign scenario has genuine common tilt equal to the selection value times that true unit polynomial vector.
Article: main_krylov, thm:select, concrete aligned spectral-sign minimax attainers.
Proof: The actual sign scenario attains the directional support and its norm is bounded by the same selection value. True Cauchy--Schwarz makes its norm equal that value; expanding the squared norm of the actual vector difference proves exact alignment. -/
theorem selection_sign_attainment (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω : Fin (N-1) → ℝ≥0) (p : ℝ[X]) (hp : p∈unitPolynomialSet base g N)
    (hmax : selectionSupport base g N ω p=selectionValue base g N ω) :
    canonicalTiltLinear base g N (selectionSignIncrements base g N ω p)=
      selectionValue base g N ω • canonicalPolynomialVector base g p := by
  -- The actual sign scenario attains its true directional support; the common-tilt norm maximum forces equality in genuine Cauchy--Schwarz.
  let v := canonicalTiltLinear base g N (selectionSignIncrements base g N ω p)
  let u := canonicalPolynomialVector base g p
  let V := selectionValue base g N ω
  have hv : ‖v‖≤V := (selectionValue_attained base g N ω).2 ⟨_,selectionSignIncrements_budget base g N ω p,rfl⟩
  have hinner : inner ℝ u v=V := (selectionSignIncrements_pairing base hb g N hN hcount ω p hp.1).trans hmax
  have hV : 0≤V := selectionValue_nonneg base g N ω
  have hn : ‖V • u‖=V := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hV,hp.2,mul_one]
  have hnv : ‖v‖=V := le_antisymm hv (by
    rw [← hinner]
    simpa only [show ‖u‖=1 from hp.2,one_mul] using real_inner_le_norm u v)
  -- Expand the genuine squared norm of the actual difference to prove exact vector alignment, including a zero selection value.
  have hz : ‖v-V • u‖^2=0 := by
    rw [norm_sub_sq_real,real_inner_smul_right,real_inner_comm u v,hinner,hn]
    rw [hnv]
    ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

/-- There exists a maximizing genuine source unit polynomial whose actual spectral-sign increments obey every true budget and attain the selection value with exact real tilt alignment.
Use: There exists a maximizing genuine source unit polynomial whose actual spectral-sign increments obey every true budget and attain the selection value with exact real tilt alignment.
Article: main_krylov, thm:select, concrete aligned spectral-sign minimax attainers.
Proof: Choose the actual attained nuclear-dual maximizer, use the concrete sign budget theorem and apply the true alignment identity. -/
theorem selection_sign_maximizer (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 2≤N) (hcount : N≤referenceAtomCount base hb g)
    (ω : Fin (N-1) → ℝ≥0) :
    ∃ p∈unitPolynomialSet base g N,
      selectionSupport base g N ω p=selectionValue base g N ω ∧
      selectionSignIncrements base g N ω p∈incrementBudget N ω ∧
      canonicalTiltLinear base g N (selectionSignIncrements base g N ω p)=
        selectionValue base g N ω • canonicalPolynomialVector base g p := by
  obtain ⟨p,hp,hmax⟩ := (selection_nuclear_dual base hb g N hN hcount ω).1
  exact ⟨p,hp,hmax,selectionSignIncrements_budget base g N ω p,
    selection_sign_attainment base hb g N hN hcount ω p hp hmax⟩
end
end krylov.Envelope
