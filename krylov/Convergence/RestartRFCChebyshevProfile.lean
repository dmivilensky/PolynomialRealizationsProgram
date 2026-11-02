import krylov.Convergence.RestartChebyshevProfile
import krylov.Functions.NativeRFCOwnSpatialResponse
import krylov.Correction.ReferenceOperator
import krylov.Correction.ConstantBounds

/-!
Article: main_krylov, thm:D, the printed ordinary RFC cubic constant.
Use: apply the sharp genuine-CG compression bound to the actual compatible
third-tensor slices, then insert the real Chebyshev error profile. The tensor
is tied to its physical variation by its true coordinate pairing.
Source: the proved sharp K(W,w) inequality and the full-reference spectral
energy measure; no independently supplied response field is used.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Finset krylov.Methods krylov.Reference krylov.Functions krylov.Tensor
  krylov.Variation krylov.Stability krylov.Design krylov.Secant krylov.Correction
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {k n : ℕ}

/-- The original ordinary-RFC cubic restart constant in terms of the
actual finite Chebyshev samples. Article: main_krylov, thm:D. -/
def rfcRestartConstant (θ : ℝ) (K : ℕ) : ℝ :=
  let W := ∑ l∈range K,jacobi.Young.sech ((l:ℝ)*θ)
  let q := jacobi.Young.sech ((K:ℝ)*θ)
  (W^2/2+W*q)*q

/-- Every genuine symmetric scalar cubic slice is a symmetric physical
matrix. Article: thm:Htransfer and thm:D. -/
theorem cubicSliceMatrix_isSymm (T : SymmetricCubic (EuclideanSpace ℝ (Fin n)))
    (v : EuclideanSpace ℝ (Fin n)) : (cubicSliceMatrix T v).IsSymm := by
  apply Matrix.isHermitian_iff_isSymm.mp
  apply Matrix.isSymmetric_toEuclideanLin_iff.mp
  change (cgOperator (cubicSliceMatrix T v)).toLinearMap.IsSymmetric
  rw [cubicSliceMatrix_operator]
  intro a b
  change inner ℝ (canonicalVariation T v a) b=inner ℝ a (canonicalVariation T v b)
  rw [real_inner_comm,canonicalVariation_pair,canonicalVariation_pair,T.swap₂]

/-- The genuine ordinary-RFC tensor coefficient obeys the exact finite
sum error profile obtained from K(W,w)≤W²/2+Ww.
Article: main_krylov, thm:D, before Chebyshev substitution. -/
theorem rfc_tensor_error_profile
    (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hA : A.PosDef)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin (k+1))))
    (hT : ∀ a b c,T.form (cgOperator (metricRoot A) a) (cgOperator (metricRoot A) b)
      (cgOperator (metricRoot A) c)=inner ℝ (D a b) c)
    (m : ℝ) (hm : 0≤m) (hdiag : ∀ v,‖v‖=1 → |T.form v v v|≤2*m)
    (g : EuclideanSpace ℝ (Fin (k+1))) (hcount : referenceAtomCount A hA g=k+1) :
    ‖rfcOwnTensorCanonicalCoefficient A hA D g‖≤
      ‖cgCanonicalError A g k‖*
        ((m*(∑ l∈range k,‖cgCanonicalError A g l‖))^2/2+
          (m*(∑ l∈range k,‖cgCanonicalError A g l‖))*(m*‖cgCanonicalError A g k‖)) := by
  have hbound (l : ℕ) (hl : l∈range ((k+1)-1)) :
      ‖ownFCCompatibleIncrements A hA D g l‖≤m*‖cgCanonicalError A g l‖ := by
    rw [ownFCCompatibleIncrements_third_tensor A hA D T hT,cubicSliceMatrix_norm]
    have hs := cubic_slice_norm_le T (2*m) (by positivity) hdiag (referenceMidpointDrift A g l)
    have hd := reference_midpoint_drift_le A hA g l (by have := mem_range.mp hl; omega)
    exact hs.trans (by nlinarith only [mul_le_mul_of_nonneg_left hd hm])
  have hsymmetric (l : ℕ) (_ : l∈range ((k+1)-1)) :
      (ownFCCompatibleIncrements A hA D g l).IsSymm := by
    rw [ownFCCompatibleIncrements_third_tensor A hA D T hT]
    exact cubicSliceMatrix_isSymm T _
  have hlast : ‖rfcOwnCompatibleCorrection A hA D g‖≤m*‖cgCanonicalError A g k‖ := by
    rw [rfcOwnCompatibleCorrection_third_tensor A hA D T hT,cubicSliceMatrix_norm,
      terminal_step_error_norm A hA g (by omega)]
    have hh := cubic_slice_norm_le T (2*m) (by positivity) hdiag
      ((1/2:ℝ) • canonicalCGStep A g k)
    simp only [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤1/2)] at hh
    nlinarith only [hh]
  have hsharp := reference_second_order_bound A hA g (by omega : k+1≤referenceAtomCount A hA g)
    (by omega : 0<k+1) (ownFCCompatibleIncrements A hA D g) hsymmetric
    (rfcOwnCompatibleCorrection A hA D g) (fun l=>m*‖cgCanonicalError A g l‖) hbound hlast
  have hnonneg : 0≤∑ l∈range ((k+1)-1),m*‖cgCanonicalError A g l‖ :=
    sum_nonneg fun _ _=>mul_nonneg hm (norm_nonneg _)
  have hu := hsharp.trans (sharpConstant_upper hnonneg (mul_nonneg hm (norm_nonneg _)))
  simp only [Nat.add_sub_cancel,←mul_sum] at hu
  rw [rfcOwnTensorCanonicalCoefficient,norm_smul,Real.norm_of_nonneg (norm_nonneg _),
    ←terminal_step_error_norm A hA g (by omega)]
  exact mul_le_mul_of_nonneg_left hu (norm_nonneg _)

set_option maxHeartbeats 800000 in
/-- The actual independent-gradient RFC tensor coefficient has the
literal printed Chebyshev cubic constant. Article: main_krylov, thm:D. -/
theorem rfc_tensor_chebyshev_constant (I : chebyshev1.SpectralInterval)
    (R : FCReference (k+1) I.mu I.kappa)
    (D : EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)) →L[ℝ] EuclideanSpace ℝ (Fin (k+1)))
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin (k+1))))
    (hT : ∀ a b c,T.form (cgOperator (metricRoot R.base) a) (cgOperator (metricRoot R.base) b)
      (cgOperator (metricRoot R.base) c)=inner ℝ (D a b) c)
    (m : ℝ) (hm : 0≤m) (hdiag : ∀ v,‖v‖=1 → |T.form v v v|≤2*m) :
    ‖rfcOwnTensorCanonicalCoefficient R.base R.positive D R.gradient‖≤
      m^2*rfcRestartConstant (designSpacing I) k*R.initialNorm^3 := by
  let W := ∑ l∈range k,‖cgCanonicalError R.base R.gradient l‖
  let A := ∑ l∈range k,jacobi.Young.sech ((l:ℝ)*designSpacing I)
  let q := jacobi.Young.sech ((k:ℝ)*designSpacing I)
  have hW : 0≤W := sum_nonneg fun _ _=>norm_nonneg _
  have hA : 0≤A := sum_nonneg fun _ _=>(jacobi.Young.sech_pos _).le
  have hq : 0≤q := (jacobi.Young.sech_pos _).le
  have hri : 0≤R.initialNorm := R.initialNorm_pos.le
  have hsum : W≤A*R.initialNorm := by
    rw [show W=∑ l∈range k,‖cgCanonicalError R.base R.gradient l‖ from rfl,
      show A*R.initialNorm=(∑ l∈range k,jacobi.Young.sech ((l:ℝ)*designSpacing I))*R.initialNorm from rfl,sum_mul]
    exact sum_le_sum fun l _=>by simpa only [epsilon_eq_sech] using reference_error_chebyshev I R l
  have hlast : ‖cgCanonicalError R.base R.gradient k‖≤q*R.initialNorm := by
    simpa only [epsilon_eq_sech] using reference_error_chebyshev I R k
  apply (rfc_tensor_error_profile R.base R.positive D T hT m hm hdiag R.gradient R.full).trans
  change ‖cgCanonicalError R.base R.gradient k‖*((m*W)^2/2+(m*W)*(m*‖cgCanonicalError R.base R.gradient k‖))≤_
  have hwm := mul_le_mul_of_nonneg_left hsum hm
  have hwl := mul_le_mul_of_nonneg_left hlast hm
  have hwm₀ : 0≤m*W := mul_nonneg hm hW
  have hwu₀ : 0≤m*(A*R.initialNorm) := mul_nonneg hm (mul_nonneg hA hri)
  have hsq := pow_le_pow_left₀ hwm₀ hwm 2
  have hmul := mul_le_mul hwm hwl (mul_nonneg hm (norm_nonneg _)) hwu₀
  have hi : (m*W)^2/2+(m*W)*(m*‖cgCanonicalError R.base R.gradient k‖)≤
      (m*(A*R.initialNorm))^2/2+(m*(A*R.initialNorm))*(m*(q*R.initialNorm)) := by
    linarith only [hsq,hmul]
  have hh := mul_le_mul hlast hi
    (add_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
      (mul_nonneg hwm₀ (mul_nonneg hm (norm_nonneg _)))) (mul_nonneg hq hri)
  exact hh.trans_eq (by unfold rfcRestartConstant; dsimp only [A,q]; ring)

end
end krylov.Convergence
