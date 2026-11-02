import jacobi.Finite.Fiber
import chebyshev1.TwoTerm.Quadratic
import chebyshev2.Finite.Gain

/-!
Endpoint-normalized Jacobi realizations, including arbitrary restarts.
Only positivity of I-J is required: off-diagonal entries may vanish and
terminal roots may repeat or equal minus one. The generic first-variation
engine and cofactor identity are the same ones used for irreducible chains.
Use: the irreducible EndpointRealization and EndpointKernel results are
specializations; the closed-fibre argument uses the full statements here.
Article: jacobi, Lemma 5.2 and Proposition 1.2.
Article role: positive prefixes and the endpoint Green-energy identity with zero-link restarts.
-/
namespace jacobi.Applications
noncomputable section
open Polynomial Matrix jacobi.Finite chebyshev1 chebyshev2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Every true leading continuant of an arbitrary original fibre is positive at one.
Use: endpoint_prefix_exact_of_posDef has all normalization denominators discharged for every fibre member, including the empty chain.
Proof: the prescribed nodes make I-J positive definite. Restrict this same pencil to the actual leading block; its positive determinant equals the genuine continuant evaluation.
Article: jacobi, Lemma 5.2 and Proposition 1.2.
-/
theorem endpoint_prefix_pos_of_posDef {N : ℕ} {J : Jacobi N}
    (hJ : (1-J.matrix).PosDef) {n : ℕ} (hn : n≤N) :
    0<(J.data.leading n).eval 1 := by
  -- Positivity comes from the original full matrix, not from an assumed prefix spectrum.
  let e : Fin n → Fin N := fun i => ⟨0+i.val,by omega⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    simpa [e] using congrArg Fin.val hij
  have hsub : (1-J.matrix).submatrix e e=1-J.data.matrix 0 n := by
    change (1:Matrix (Fin N) (Fin N) ℝ).submatrix e e-
      (J.data.matrix 0 N).submatrix e e=_
    rw [J.data.matrix_principal_block N 0 n (by omega)]
    simp only [Matrix.submatrix_one e he]
  have hd := (hJ.submatrix he).det_pos
  rw [hsub] at hd
  rw [JacobiData.leading,J.data.block_eq_charpoly J.coupling_nonneg,Matrix.eval_charpoly]
  simpa [Matrix.scalar] using hd

/-- The original leading polynomial normalized at one and expressed in the physical residual coordinate.
Use: endpoint_prefix_exact identifies every actual two-step prefix with this genuine polynomial.
Article: jacobi, Lemma 5.2 and Proposition 1.2.
-/
def endpointResidual {N : ℕ} (J : Jacobi N) (n : ℕ) : Polynomial ℝ :=
  C ((J.data.leading n).eval 1)⁻¹*(J.data.leading n).comp (1-C 2*X)

/-- The original endpoint-normalized residual evaluates to the literal normalized continuant ratio.
Use: prefix exactness and terminal identification reduce to the same actual Jacobi recurrence and full node product.
Proof: evaluate the polynomial product and affine composition.
Article: jacobi, Lemma 5.2 and Proposition 1.2.
-/
theorem endpointResidual_eval {N : ℕ} (J : Jacobi N) (n : ℕ) (l : ℝ) :
    (endpointResidual J n).eval l=(J.data.leading n).eval (1-2*l)/(J.data.leading n).eval 1 := by
  simp only [endpointResidual,eval_mul,eval_C,eval_comp,eval_sub,eval_one,eval_X]
  ring

/-- The genuine two-step semi-iterative method attached to any original Jacobi chain at the residual endpoint.
Use: endpoint_prefix_exact reuses the earlier verified TwoTerm engine and terminal_realization appends the exact Landweber steps.
Article: jacobi, Lemma 5.2 and Proposition 1.2.
-/
def endpointMethod {N : ℕ} (J : Jacobi N) : TwoTerm where
  a i := (1-J.data.b i)*(J.data.leading i).eval 1/(J.data.leading (i+1)).eval 1
  b i := -(J.data.aSq i*(J.data.leading (i-1)).eval 1/(J.data.leading (i+1)).eval 1)
  gamma i := 2*(J.data.leading i).eval 1/(J.data.leading (i+1)).eval 1

/-- Every actual two-step residual prefix equals the corresponding original normalized Jacobi continuant.
Use: endpoint_terminal_exact identifies an arbitrary fibre realization's terminal residual without selecting special weights or a persymmetric chain.
Proof: apply the already verified TwoTerm polynomial recurrence. Its two initial values and every later step are the original monic continuant recurrence divided by genuine positive prefix values.
Article: jacobi, Lemma 5.2 and Proposition 1.2.
-/
theorem endpoint_prefix_exact_of_posDef {N : ℕ} {J : Jacobi N}
    (hJ : (1-J.matrix).PosDef) (n : ℕ) (hn : n≤N) :
    (endpointMethod J).realization.residualPolynomial n=endpointResidual J n := by
  -- The previous article supplies the actual iteration semantics; only the new endpoint normalization is proved here.
  induction n using Nat.twoStepInduction with
  | zero => simp [TwoTerm.residual_zero,endpointResidual]
  | one =>
    rw [TwoTerm.residual_one]
    apply Polynomial.funext
    intro l
    have hden := (endpoint_prefix_pos_of_posDef hJ hn).ne'
    simp only [JacobiData.leading_one,eval_sub,eval_X,eval_C] at hden
    rw [endpointResidual_eval]
    simp [endpointMethod,JacobiData.leading_one]
    field_simp
    ring
  | more n h0 h1 =>
    rw [TwoTerm.residual_recurrence,h0 (by omega),h1 (by omega)]
    apply Polynomial.funext
    intro l
    have hrec : J.data.leading (n+2)=(X-C (J.data.b (n+1)))*J.data.leading (n+1)-
        C (J.data.aSq (n+1))*J.data.leading n := by
      simp only [JacobiData.leading,JacobiData.block,Nat.zero_add]
    have hd0 := (endpoint_prefix_pos_of_posDef hJ (show n≤N by omega)).ne'
    have hd1 := (endpoint_prefix_pos_of_posDef hJ (show n+1≤N by omega)).ne'
    have hd2 := (endpoint_prefix_pos_of_posDef hJ hn).ne'
    simp only [eval_add,eval_sub,eval_mul,eval_C,eval_X,endpointResidual_eval,
      endpointMethod,Nat.add_sub_cancel]
    rw [hrec]
    simp only [eval_sub,eval_mul,eval_X,eval_C]
    field_simp
    ring

/-- Every genuine endpoint method step preserves the fixed point, including the initial zero-coupling step.
Use: endpoint_method_signs_of_posDef identifies the source recurrence coefficients a_i=1+delta_i and b_i=-delta_i for an arbitrary original fibre member.
Proof: the original continuant recurrence evaluated at one gives the exact denominator identity. At the initial step the incoming coupling is zero and p_0(1)=1.
Article: jacobi, Lemma 5.2 and Proposition 1.2.
-/
theorem endpoint_method_fixed_point_of_posDef {N : ℕ} {J : Jacobi N}
    (hJ : (1-J.matrix).PosDef) {i : ℕ} (hi : i<N) :
    (endpointMethod J).a i+(endpointMethod J).b i=1 := by
  -- The denominator is an actual positive prefix determinant before either recurrence case is simplified.
  have hd := (endpoint_prefix_pos_of_posDef hJ (show i+1≤N by omega)).ne'
  cases i with
  | zero =>
    simp only [endpointMethod,J.coupling_zero,Nat.zero_add,zero_mul,zero_div,neg_zero,add_zero,
      JacobiData.leading_zero,JacobiData.leading_one,eval_one,eval_sub,eval_X,eval_C,mul_one]
    simpa only [Nat.zero_add,JacobiData.leading_one,eval_sub,eval_X,eval_C] using div_self hd
  | succ i =>
    have hrec : (J.data.leading (i+2)).eval 1=
        (1-J.data.b (i+1))*(J.data.leading (i+1)).eval 1-
          J.data.aSq (i+1)*(J.data.leading i).eval 1 := by
      simp only [JacobiData.leading,JacobiData.block,Nat.zero_add,eval_sub,eval_mul,eval_X,eval_C]
    simp only [endpointMethod,Nat.add_sub_cancel,← sub_eq_add_neg,
      ← sub_div,← hrec]
    exact div_self hd

/-- Every actual endpoint step has positive step size, nonnegative momentum delta=-b, and the exact fixed-point coefficient a=1+delta.
Use: the arbitrary-fibre realization is the genuine two-step semi-iterative scheme displayed in the source, with every sign and normalization proved.
Proof: all three actual prefix determinants are positive, and the original squared coupling is nonnegative. Combine these signs with the proved continuant fixed-point identity.
Article: jacobi, Lemma 5.2 and Proposition 1.2.
-/
theorem endpoint_method_signs_of_posDef {N : ℕ} {J : Jacobi N}
    (hJ : (1-J.matrix).PosDef) {i : ℕ} (hi : i<N) :
    0<(endpointMethod J).gamma i ∧ (endpointMethod J).b i≤0 ∧
      (endpointMethod J).a i=1-(endpointMethod J).b i := by
  have hp := endpoint_prefix_pos_of_posDef hJ (show i≤N by omega)
  have hq := endpoint_prefix_pos_of_posDef hJ (show i+1≤N by omega)
  have hr := endpoint_prefix_pos_of_posDef hJ (show i-1≤N by omega)
  refine ⟨div_pos (mul_pos (by norm_num) hp) hq,neg_nonpos.mpr
    (div_nonneg (mul_nonneg (J.coupling_nonneg i) hr.le) hq.le),?_⟩
  linarith [endpoint_method_fixed_point_of_posDef hJ hi]

/-- A nonempty actual endpoint-normalized Jacobi tail is its genuine right-block continuant with the exact two prefix normalizations.
Use: endpoint_kernel_of_posDef identifies the actual original first variation on [0,1].
Proof: the same causal two-term engine as in chebyshev1 is used at pole one. Each matrix multiplication gives the actual monic block recurrence; the proved positive prefix values justify every cancellation.
Article: jacobi, Lemma 5.2 and Proposition 1.2.
-/
theorem endpoint_tail_column_of_posDef {N:ℕ} {J:Jacobi N} (hJ:(1-J.matrix).PosDef)
    (r k:ℕ) (hr:1≤r) (hk:r+(k+1)≤N) (l:ℝ) :
    let M := orderedProduct (fun i => (endpointMethod J).realization.scalarStep (r+i) l) (k+1)
    M 0 0=(J.data.leading r).eval 1/(J.data.leading (r+(k+1))).eval 1*
      (J.data.block r (k+1)).eval (1-2*l) ∧
    M 1 0=(J.data.leading r).eval 1/(J.data.leading (r+k)).eval 1*(J.data.block r k).eval (1-2*l) := by
  -- The original tail and prefix polynomials are retained, including the empty complementary block.
  induction k with
  | zero =>
    simp only [orderedProduct_succ,orderedProduct_zero,mul_one,Nat.add_zero]
    rw [show r=(r-1)+1 by omega,TwoTerm.scalarStep_succ]
    simp only [show r-1+1=r by omega]
    constructor
    · simp [endpointMethod,JacobiData.block]
      ring
    · simp [endpointMethod,JacobiData.block,(endpoint_prefix_pos_of_posDef hJ (show r≤N by omega)).ne']
  | succ k ih =>
    have hh := ih (by omega)
    dsimp only at hh ⊢
    rw [orderedProduct_succ,show r+(k+1)=(r+k)+1 by omega,TwoTerm.scalarStep_succ]
    constructor
    · simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val_fin_one]
      rw [hh.1,hh.2]
      simp only [endpointMethod,Nat.add_sub_cancel]
      have hc : (J.data.block r (k+2)).eval (1-2*l)=
          (1-2*l-J.data.b (r+k+1))*(J.data.block r (k+1)).eval (1-2*l)-
            J.data.aSq (r+k+1)*(J.data.block r k).eval (1-2*l) := by simp [JacobiData.block]
      simp only [Nat.add_assoc]
      rw [hc]
      have hd0 := endpoint_prefix_pos_of_posDef hJ (show r+k≤N by omega)
      have hd1 := endpoint_prefix_pos_of_posDef hJ (show r+k+1≤N by omega)
      have hd2 := endpoint_prefix_pos_of_posDef hJ (show r+k+2≤N by omega)
      simp only [Nat.add_assoc] at hd0 hd1 hd2
      field_simp [hd0.ne',hd1.ne',hd2.ne']
      ring
    · simpa only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply,Matrix.cons_val_zero,
        Matrix.cons_val_one,Matrix.cons_val_fin_one,one_mul,zero_mul,add_zero,Nat.add_assoc] using hh.1

/-- The true endpoint-normalized Jacobi insertion tail has its exact genuine block formula, including the empty tail.
Use: endpoint_kernel_of_posDef separates the original forward and backward continuants of each actual Hessian insertion.
Proof: the empty product is the identity; every nonempty product is the proved original two-entry tail column.
Article: jacobi, Lemma 5.2 and Proposition 1.2.
-/
theorem endpoint_tail_fundamental_of_posDef {N:ℕ} {J:Jacobi N} (hJ:(1-J.matrix).PosDef)
    {r:ℕ} (hr:1≤r) (hrN:r≤N) (l:ℝ) :
    orderedProduct (fun i => (endpointMethod J).realization.scalarStep (r+i) l) (N-r) 0 0=
      (J.data.leading r).eval 1/(J.data.leading N).eval 1*(J.data.block r (N-r)).eval (1-2*l) := by
  -- Separate the literal empty tail before reindexing the positive-length continuant column.
  rcases Nat.eq_zero_or_pos (N-r) with he | hp
  · have hN : N=r := by omega
    subst N
    simp [JacobiData.block,(endpoint_prefix_pos_of_posDef hJ hrN).ne']
  · obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
    have hh := (endpoint_tail_column_of_posDef hJ r k hr (by omega) l).1
    have ht : r+(k+1)=N := by omega
    rw [ht] at hh
    simpa only [hk,Nat.succ_eq_add_one] using hh

/-- The actual original endpoint Jacobi realization has the exact two-sided continuant first-variation kernel on the unit spectral interval.
Use: endpoint_kernel_green_of_posDef and BlockKernel transfer its full endpoint time norm to the actual original inverse energy.
Proof: expand the reused actual rank-one two-term kernel. The proved true tail gives its right block, while the already proved exact prefix polynomial gives its left block. Positive genuine prefix values cancel the intermediate normalization.
Article: jacobi, Lemma 5.2 and Proposition 1.2.
-/
theorem endpoint_kernel_of_posDef {N:ℕ} {J:Jacobi N} (hJ:(1-J.matrix).PosDef)
    {s:ℕ} (hs:s<N) (l v:ℝ) :
    (endpointMethod J).realization.kernel N s l v=
      -2*(J.data.leading s).eval (1-2*v)*(J.data.block (s+1) (N-(s+1))).eval (1-2*l)/
        (J.data.leading N).eval 1 := by
  -- The real first variation is inherited from the earlier operator-transfer theorem, not defined by the desired formula.
  have hf : (endpointMethod J).realization.scalarTransfer s v=
      (J.data.leading s).eval (1-2*v)/(J.data.leading s).eval 1 := by
    rw [← Realization.residualPolynomial_eval,endpoint_prefix_exact_of_posDef hJ s hs.le,endpointResidual_eval]
  have hk : (endpointMethod J).realization.kernel N s l v=
      -(orderedProduct (fun i => (endpointMethod J).realization.scalarStep (s+1+i) l) (N-(s+1)) 0 0*
        (endpointMethod J).gamma s*(endpointMethod J).realization.scalarTransfer s v) := by
    simp [Realization.kernel,Realization.scalarTransfer,Matrix.mul_apply,Fin.sum_univ_two]
  rw [hk,endpoint_tail_fundamental_of_posDef hJ (by omega) (by omega),hf]
  dsimp [endpointMethod]
  field_simp [(endpoint_prefix_pos_of_posDef hJ hs.le).ne',(endpoint_prefix_pos_of_posDef hJ (show s+1≤N by omega)).ne']

/-- Every original unit-interval Jacobi insertion at zero is exactly minus twice the corresponding actual resolvent diagonal.
Use: the appended-block endpoint time norm is exactly 4*E(J)+d over the complete original fibre.
Proof: substitute the actual kernel factorization and the genuine finite cofactor formula for the same inverse matrix.
Article: jacobi, Lemma 5.2 and Proposition 1.2.
-/
theorem endpoint_kernel_green_of_posDef {N:ℕ} {J:Jacobi N} (hJ:(1-J.matrix).PosDef) (s:Fin N) :
    (endpointMethod J).realization.kernel N s.val 0 0=-2*J.green s s := by
  rw [endpoint_kernel_of_posDef hJ s.isLt,Jacobi.green_diagonal J (Nat.zero_lt_of_lt s.isLt)]
  norm_num
  ring

/-- The actual original unit-interval endpoint time norm equals precisely twice the square root of the original inverse energy.
Use: the complete package checks the exact zero-lower-endpoint conclusion of Energy and endpoint drift for the same original Jacobi realization.
Proof: every genuine endpoint kernel is minus twice its original inverse diagonal. Sum those exact squared values over the original vertices and take the nonnegative square root.
Article: jacobi, Lemma 5.2 and Proposition 1.2.
-/
theorem endpoint_gain_energy_of_posDef {N:ℕ} {J:Jacobi N} (hJ:(1-J.matrix).PosDef) :
    (endpointMethod J).realization.kernelNorm N 0 0=2*Real.sqrt J.energy := by
  -- The exact finite norm uses the same endpoint kernels and the same original Green matrix throughout.
  have he:(∑ i:Fin N,((endpointMethod J).realization.kernel N i 0 0)^2)=4*J.energy:=by
    rw [Jacobi.energy,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [endpoint_kernel_green_of_posDef hJ i]
    ring
  rw [Fin.sum_univ_eq_sum_range (f:=fun i:ℕ=>((endpointMethod J).realization.kernel N i 0 0)^2)] at he
  rw [Realization.kernelNorm,he,Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
  norm_num

end
end jacobi.Applications
