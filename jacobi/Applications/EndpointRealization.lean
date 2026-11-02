import jacobi.Applications.ClosedEndpoint

/-!
Article: jacobi, Proposition 1.2.
Principal-pencil positivity proves every denominator, including empty
prefixes; no interlacing hypothesis is left to the caller.
Source: positivity of principal submatrices and the continuant recurrence.
Use: endpoint_prefix_exact has all normalization denominators discharged for every fibre member, including the empty chain.
-/
namespace jacobi.Applications
noncomputable section
open Polynomial Matrix jacobi.Finite chebyshev1 chebyshev2
set_option backward.isDefEq.respectTransparency false

/-- Every true leading continuant of an arbitrary original fibre is positive at one.
Use: endpoint_prefix_exact has all normalization denominators discharged for every fibre member, including the empty chain.
Article: jacobi, Proposition 1.2.
Proof: the prescribed nodes make I-J positive definite. Restrict this same pencil to the actual leading block; its positive determinant equals the genuine continuant evaluation. -/
theorem endpoint_prefix_pos {N : ℕ} (S : Nodes N) {J : Jacobi N}
    (hJ : InFiber J S.polynomial) {n : ℕ} (hn : n≤N) :
    0<(J.data.leading n).eval 1 := by
  have hp : (1-J.matrix).PosDef := by
    have h := J.affine_posDef 1 (-1) (fun x hx => by
      rw [S.spectrum_eq hJ] at hx
      obtain ⟨i,rfl⟩ := hx
      linarith [(S.interval i).2])
    simpa [Matrix.scalar,sub_eq_add_neg] using h
  exact endpoint_prefix_pos_of_posDef hp hn

/-- Every actual two-step residual prefix equals the corresponding original normalized Jacobi continuant.
Use: endpoint_terminal_exact identifies an arbitrary fibre realization's terminal residual without selecting special weights or a persymmetric chain.
Article: jacobi, Proposition A.1.
Proof: apply the already verified TwoTerm polynomial recurrence. Its two initial values and every later step are the original monic continuant recurrence divided by genuine positive prefix values. -/
theorem endpoint_prefix_exact {N : ℕ} (S : Nodes N) {J : Jacobi N}
    (hJ : InFiber J S.polynomial) (n : ℕ) (hn : n≤N) :
    (endpointMethod J).realization.residualPolynomial n=endpointResidual J n := by
  exact endpoint_prefix_exact_of_posDef (by
    have h := J.affine_posDef 1 (-1) (fun x hx => by
      rw [S.spectrum_eq hJ] at hx
      obtain ⟨i,rfl⟩ := hx
      linarith [(S.interval i).2])
    simpa [Matrix.scalar,sub_eq_add_neg] using h) n hn

/-- Every genuine endpoint method step preserves the fixed point, including the initial zero-coupling step.
Use: endpoint_method_signs identifies the source recurrence coefficients a_i=1+delta_i and b_i=-delta_i for an arbitrary original fibre member.
Article: jacobi, Proposition A.1.
Proof: the original continuant recurrence evaluated at one gives the exact denominator identity. At the initial step the incoming coupling is zero and p_0(1)=1. -/
theorem endpoint_method_fixed_point {N : ℕ} (S : Nodes N) {J : Jacobi N}
    (hJ : InFiber J S.polynomial) {i : ℕ} (hi : i<N) :
    (endpointMethod J).a i+(endpointMethod J).b i=1 := by
  exact endpoint_method_fixed_point_of_posDef (by
    have h := J.affine_posDef 1 (-1) (fun x hx => by
      rw [S.spectrum_eq hJ] at hx
      obtain ⟨i,rfl⟩ := hx
      linarith [(S.interval i).2])
    simpa [Matrix.scalar,sub_eq_add_neg] using h) hi

/-- Every actual endpoint step has positive step size, nonnegative momentum delta=-b, and the exact fixed-point coefficient a=1+delta.
Use: the arbitrary-fibre realization is the genuine two-step semi-iterative scheme displayed in the source, with every sign and normalization proved.
Article: jacobi, Proposition A.1.
Proof: all three actual prefix determinants are positive, and the original squared coupling is nonnegative. Combine these signs with the proved continuant fixed-point identity. -/
theorem endpoint_method_signs {N : ℕ} (S : Nodes N) {J : Jacobi N}
    (hJ : InFiber J S.polynomial) {i : ℕ} (hi : i<N) :
    0<(endpointMethod J).gamma i ∧ (endpointMethod J).b i≤0 ∧
      (endpointMethod J).a i=1-(endpointMethod J).b i := by
  exact endpoint_method_signs_of_posDef (by
    have h := J.affine_posDef 1 (-1) (fun x hx => by
      rw [S.spectrum_eq hJ] at hx
      obtain ⟨i,rfl⟩ := hx
      linarith [(S.interval i).2])
    simpa [Matrix.scalar,sub_eq_add_neg] using h) hi

end
end jacobi.Applications
