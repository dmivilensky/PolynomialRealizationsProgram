import jacobi.Applications.EndpointRealization
import chebyshev2.Finite.Gain

/-!
Article: jacobi, Proposition 1.2.
The original endpoint-normalized Jacobi method has the genuine two-sided
continuant first-variation kernel. Every normalization denominator is
proved positive for every member of the complete original fibre.
Use: BlockKernel converts its endpoint channel to exactly four times the
original resolvent energy, before the final Landweber stage is appended.
-/
namespace jacobi.Applications
noncomputable section
open Polynomial Matrix jacobi.Finite chebyshev1 chebyshev2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- A nonempty actual endpoint-normalized Jacobi tail is its genuine right-block continuant with the exact two prefix normalizations.
Use: endpoint_kernel identifies the actual original first variation on [0,1].
Article: jacobi, Proposition 1.2.
Proof: the same causal two-term engine as in chebyshev1 is used at pole one. Each matrix multiplication gives the actual monic block recurrence; the proved positive prefix values justify every cancellation. -/
theorem endpoint_tail_column {N:ℕ} (S:Nodes N) {J:Jacobi N} (hJ:InFiber J S.polynomial)
    (r k:ℕ) (hr:1≤r) (hk:r+(k+1)≤N) (l:ℝ) :
    let M := orderedProduct (fun i => (endpointMethod J).realization.scalarStep (r+i) l) (k+1)
    M 0 0=(J.data.leading r).eval 1/(J.data.leading (r+(k+1))).eval 1*
      (J.data.block r (k+1)).eval (1-2*l) ∧
    M 1 0=(J.data.leading r).eval 1/(J.data.leading (r+k)).eval 1*(J.data.block r k).eval (1-2*l) := by
  exact endpoint_tail_column_of_posDef (by
    have h := J.affine_posDef 1 (-1) (fun x hx => by
      rw [S.spectrum_eq hJ] at hx
      obtain ⟨i,rfl⟩ := hx
      linarith [(S.interval i).2])
    simpa [Matrix.scalar,sub_eq_add_neg] using h) r k hr hk l

/-- The true endpoint-normalized Jacobi insertion tail has its exact genuine block formula, including the empty tail.
Use: endpoint_kernel separates the original forward and backward continuants of each actual Hessian insertion.
Article: jacobi, Proposition 1.2.
Proof: the empty product is the identity; every nonempty product is the proved original two-entry tail column. -/
theorem endpoint_tail_fundamental {N:ℕ} (S:Nodes N) {J:Jacobi N} (hJ:InFiber J S.polynomial)
    {r:ℕ} (hr:1≤r) (hrN:r≤N) (l:ℝ) :
    orderedProduct (fun i => (endpointMethod J).realization.scalarStep (r+i) l) (N-r) 0 0=
      (J.data.leading r).eval 1/(J.data.leading N).eval 1*(J.data.block r (N-r)).eval (1-2*l) := by
  exact endpoint_tail_fundamental_of_posDef (by
    have h := J.affine_posDef 1 (-1) (fun x hx => by
      rw [S.spectrum_eq hJ] at hx
      obtain ⟨i,rfl⟩ := hx
      linarith [(S.interval i).2])
    simpa [Matrix.scalar,sub_eq_add_neg] using h) hr hrN l

/-- The actual original endpoint Jacobi realization has the exact two-sided continuant first-variation kernel on the unit spectral interval.
Use: endpoint_kernel_green and BlockKernel transfer its full endpoint time norm to the actual original inverse energy.
Article: jacobi, Proposition 1.2.
Proof: expand the reused actual rank-one two-term kernel. The proved true tail gives its right block, while the already proved exact prefix polynomial gives its left block. Positive genuine prefix values cancel the intermediate normalization. -/
theorem endpoint_kernel {N:ℕ} (S:Nodes N) {J:Jacobi N} (hJ:InFiber J S.polynomial)
    {s:ℕ} (hs:s<N) (l v:ℝ) :
    (endpointMethod J).realization.kernel N s l v=
      -2*(J.data.leading s).eval (1-2*v)*(J.data.block (s+1) (N-(s+1))).eval (1-2*l)/
        (J.data.leading N).eval 1 := by
  exact endpoint_kernel_of_posDef (by
    have h := J.affine_posDef 1 (-1) (fun x hx => by
      rw [S.spectrum_eq hJ] at hx
      obtain ⟨i,rfl⟩ := hx
      linarith [(S.interval i).2])
    simpa [Matrix.scalar,sub_eq_add_neg] using h) hs l v

/-- Every original unit-interval Jacobi insertion at zero is exactly minus twice the corresponding actual resolvent diagonal.
Use: the appended-block endpoint time norm is exactly 4*E(J)+d over the complete original fibre.
Article: jacobi, Proposition 1.2.
Proof: substitute the actual kernel factorization and the genuine finite cofactor formula for the same inverse matrix. -/
theorem endpoint_kernel_green {N:ℕ} (S:Nodes N) {J:Jacobi N} (hJ:InFiber J S.polynomial) (s:Fin N) :
    (endpointMethod J).realization.kernel N s.val 0 0=-2*J.green s s := by
  exact endpoint_kernel_green_of_posDef (by
    have h := J.affine_posDef 1 (-1) (fun x hx => by
      rw [S.spectrum_eq hJ] at hx
      obtain ⟨i,rfl⟩ := hx
      linarith [(S.interval i).2])
    simpa [Matrix.scalar,sub_eq_add_neg] using h) s

/-- The actual original unit-interval endpoint time norm equals precisely twice the square root of the original inverse energy.
Use: Article checks the exact zero-lower-endpoint conclusion of Energy and endpoint drift for the same original Jacobi realization.
Article: jacobi, Proposition 1.2.
Proof: every genuine endpoint kernel is minus twice its original inverse diagonal. Sum those exact squared values over the original vertices and take the nonnegative square root. -/
theorem endpoint_gain_energy {N:ℕ} (S:Nodes N) {J:Jacobi N} (hJ:InFiber J S.polynomial) :
    (endpointMethod J).realization.kernelNorm N 0 0=2*Real.sqrt J.energy := by
  exact endpoint_gain_energy_of_posDef (by
    have h := J.affine_posDef 1 (-1) (fun x hx => by
      rw [S.spectrum_eq hJ] at hx
      obtain ⟨i,rfl⟩ := hx
      linarith [(S.interval i).2])
    simpa [Matrix.scalar,sub_eq_add_neg] using h)

end
end jacobi.Applications
