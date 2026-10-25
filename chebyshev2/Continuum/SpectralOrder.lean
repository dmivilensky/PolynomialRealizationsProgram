import chebyshev2.Continuum.SpectralQuadratic

/-!
Article: chebyshev2, Proposition 2.
Eigenvalue monotonicity, proved by the dimension argument behind min--max.
Use: `chebyshev2.Continuum.eigenvalue_basis_independent` feeds
`chebyshev2.Continuum.eigenvalue_eq_of_operator_eq` (eigenvalue eq of operator eq).
Proof chain: `chebyshev2.Packing.packed_spectral_distance` — chebyshev2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory. The needed
form is proved here.
-/
namespace chebyshev2.Continuum
noncomputable section
open Submodule Module
open scoped InnerProductSpace BigOperators Classical
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
Eigenvalue monotonicity, proved by the dimension argument behind min--max. It also proves that
the sorted spectrum is independent of the chosen basis.

The stated quantitative bound `DA.eigenvalue n ≤ DB.eigenvalue n`.

Use: `chebyshev2.Continuum.eigenvalue_basis_independent` uses this bound to establish exact
identity `D.eigenvalue = D'.eigenvalue`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Assume the failure of the desired conclusion and derive a contradiction from the
available bounds/identities.
-/
theorem eigenvalue_mono {A B : E →L[ℝ] E} (DA : PositiveSpectralData A) (DB : PositiveSpectralData B)
    (hAB : ∀ x, inner ℝ x (A x) ≤ inner ℝ x (B x)) (n : ℕ) : DA.eigenvalue n ≤ DB.eigenvalue n := by
  -- Assume the failure of the desired conclusion and derive a contradiction from the available
  -- bounds/identities.
  by_contra! hlt
  have hp : 0 < DA.eigenvalue n := (DB.eigenvalue_nonneg n).trans_lt hlt
  let sA := spectralSelected DA.summable (n+1)
  let sB := spectralSelected DB.summable n
  have hcardA : sA.card = n+1 := by
    cases h : spectralNext DA.summable (spectralSelected DA.summable n) with
    | none =>
      have hz : DA.eigenvalue n = 0 := by simp only [PositiveSpectralData.eigenvalue,spectralSorted,h,Option.elim_none]
      exact (hp.ne' hz).elim
    | some i =>
      dsimp [sA]
      rw [spectralSelected,h,Finset.card_insert_of_notMem (spectralNext_some DA.summable h).1,
        spectralSelected_card_of_missing DA.summable n (spectralNext_some DA.summable h).1
          (spectralNext_some DA.summable h).2.1]
  have hcardB : sB.card ≤ n := spectralSelected_card_le DB.summable n
  let SA := span ℝ (Set.range (fun i : sA => DA.basis i))
  let φ : SA →ₗ[ℝ] (sB → ℝ) := LinearMap.pi (fun j =>
    ((innerSL ℝ (DB.basis j)).toLinearMap).comp SA.subtype)
  have hdimA : finrank ℝ SA = n+1 := by
    change finrank ℝ (span ℝ (Set.range (DA.basis ∘ (fun i : sA => (i : DA.Index))))) = n+1
    rw [finrank_span_eq_card (DA.basis.orthonormal.linearIndependent.comp
      (fun i : sA => (i : DA.Index)) Subtype.coe_injective)]
    simpa using hcardA
  have hdimB : finrank ℝ (sB → ℝ) ≤ n := by
    rw [Module.finrank_pi]
    simpa using hcardB
  have hker : φ.ker ≠ ⊥ := by
    intro hker
    have h := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp hker)
    rw [hdimA] at h
    omega
  obtain ⟨u,hu,hune⟩ := φ.ker.ne_bot_iff.mp hker
  have hun : (u : E) ≠ 0 := fun hh => hune (Subtype.ext hh)
  have huB : ∀ j ∈ spectralSelected DB.summable n, inner ℝ (DB.basis j) (u : E) = 0 := by
    intro j hj
    have h := congrFun (LinearMap.mem_ker.mp hu) (⟨j,hj⟩ : sB)
    exact h
  have huA : ∀ j ∉ spectralSelected DA.summable (n+1), inner ℝ (DA.basis j) (u : E) = 0 := by
    intro j hj
    apply span_induction (p := fun x _ => inner ℝ (DA.basis j) x = 0) _ _ _ _ u.property
    · rintro x ⟨i,rfl⟩
      exact DA.basis.orthonormal.inner_eq_zero (fun he => hj (he ▸ i.property))
    · simp
    · intro x y hx hy hx' hy'
      simp [inner_add_right,hx',hy']
    · intro c x hx hx'
      simp [real_inner_smul_right,hx']
  have hlow := DA.quadratic_ge_of_selected n (u : E) huA
  have hhigh := DB.quadratic_le_eigenvalue n (u : E) huB
  have hnorm : 0 < ‖(u : E)‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hun)
  have hquad := hAB (u : E)
  nlinarith

/--
Exact identity `D.eigenvalue = D'.eigenvalue`.

Use: `chebyshev2.Continuum.diagonal_matrix_eigenvalue` uses this identity to establish
exact identity `(matrixSpectralData (Matrix.diagonal a) (Matrix.posSemidef_diagonal_iff.mpr
ha)).eigenvalue = spectralSorted (Summable.of_finite (f := a))`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Riesz and Sz.-Nagy, Functional Analysis — compact self-adjoint spectral theory.

Proof: Prove equality of functions by evaluating both sides at an arbitrary argument.
-/
theorem eigenvalue_basis_independent {T : E →L[ℝ] E} (D D' : PositiveSpectralData T) :
    D.eigenvalue = D'.eigenvalue := by
  funext n
  exact le_antisymm (eigenvalue_mono D D' (fun _ => le_rfl) n)
    (eigenvalue_mono D' D (fun _ => le_rfl) n)

end
end chebyshev2.Continuum
