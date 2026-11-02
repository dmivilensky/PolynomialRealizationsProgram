import krylov.Reference.PolynomialAction

/-!
Article: main_krylov, apB:lem:filtration and apB:eq:F1, genuine Krylov flag propagation.
Use: preserve the actual polynomial Krylov indexing, including the empty
space, under true reference operator action and finite prefix enlargement.
Source: the existing actual polynomialAction/krylovSpace, mathlib degreeLT
monotonicity and the genuine polynomial degree of multiplication by X.
-/

namespace krylov.Envelope
noncomputable section
open Polynomial krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine polynomial Krylov flags increase with the actual reference horizon.
Use: The genuine polynomial Krylov flags increase with the actual reference horizon.
Article: main_krylov, apB:lem:filtration and apB:eq:F1, genuine Krylov flag propagation.
Proof: Map the standard polynomial degree-subspace inclusion through the true physical polynomial action. -/
theorem krylovSpace_mono (Q : E →L[ℝ] E) (g : E) {i j : ℕ} (hij : i ≤ j) :
    CG.krylovSpace Q g i ≤ CG.krylovSpace Q g j := by
  exact Submodule.map_mono (Polynomial.degreeLT_mono hij)

/-- Multiplying the true polynomial response by X applies the actual physical reference operator.
Use: Multiplying the true polynomial response by X applies the actual physical reference operator.
Article: main_krylov, apB:lem:filtration and apB:eq:F1, genuine Krylov flag propagation.
Proof: The genuine polynomial evaluation algebra homomorphism preserves multiplication. -/
theorem polynomialAction_X_mul (Q : E →L[ℝ] E) (g : E) (p : ℝ[X]) :
    CG.polynomialAction Q g (X*p)=Q (CG.polynomialAction Q g p) := by
  simp [CG.polynomialAction,map_mul,aeval_X,mul_apply_eq_comp]

/-- The true reference operator sends every genuine order-k Krylov vector into the actual next Krylov flag.
Use: The true reference operator sends every genuine order-k Krylov vector into the actual next Krylov flag.
Article: main_krylov, apB:lem:filtration and apB:eq:F1, genuine Krylov flag propagation.
Proof: Represent the real vector by its true polynomial, multiply that polynomial by X and prove the genuine next degree bound, including the zero polynomial. -/
theorem krylovSpace_operator (Q : E →L[ℝ] E) (g : E) (k : ℕ) {v : E}
    (hv : v∈CG.krylovSpace Q g k) : Q v∈CG.krylovSpace Q g (k+1) := by
  -- Use the actual polynomial witness and treat its zero case before passing from degree to natural degree.
  obtain ⟨p,hp,rfl⟩ := hv
  by_cases hp0 : p=0
  · subst p
    simp only [map_zero]
    exact Submodule.zero_mem _
  have hdegree : p.natDegree < k := by
    have hd := Polynomial.mem_degreeLT.mp hp
    rw [Polynomial.degree_eq_natDegree hp0] at hd
    exact_mod_cast hd
  have hx : X*p∈degreeLT ℝ (k+1) := by
    apply Polynomial.mem_degreeLT.mpr
    rw [Polynomial.degree_eq_natDegree (mul_ne_zero X_ne_zero hp0),Polynomial.natDegree_X_mul hp0]
    exact_mod_cast Nat.succ_lt_succ hdegree
  exact ⟨X*p,hx,polynomialAction_X_mul Q g p⟩

/-- Every true nondegenerate computed reference direction belongs to its genuine next polynomial Krylov flag.
Use: Every true nondegenerate computed reference direction belongs to its genuine next polynomial Krylov flag.
Article: main_krylov, apB:lem:filtration and apB:eq:F1, genuine Krylov flag propagation.
Proof: Use the already proved equality between the actual direction span and the true polynomial flag. -/
theorem cgDirection_mem_krylov (Q : E →L[ℝ] E) (g : E) (k : ℕ)
    (hline : ∀ i < k+1, CG.length Q g i≠0) : CG.direction Q g k∈CG.krylovSpace Q g (k+1) := by
  rw [CG.krylovSpace_eq_span_directions Q g (k+1) hline]
  exact Submodule.subset_span ⟨k,Nat.lt_succ_self k,rfl⟩
end
end krylov.Envelope
