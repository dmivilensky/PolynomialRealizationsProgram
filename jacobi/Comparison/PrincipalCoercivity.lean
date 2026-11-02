import jacobi.Comparison.UniformCoercivity
import jacobi.Comparison.Schur
import jacobi.Analysis.ZeroExtension

/-!
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Use: principalGram_uniform_coercive applies it to the exact blocks whose inverses define the actual source Cholesky rows.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set jacobi.Analysis jacobi.Finite

/-- Every injectively selected original physical principal section has
the same strictly positive uniform lower bound, independent of its size.
Use: principalGram_uniform_coercive applies it to the exact blocks whose
inverses define the actual source Cholesky rows.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: extend the actual finite vector by zero to the original matrix.
Its true image lies in the physical half. The proved full half-prefix
bound applies, and both its norm and complete form transport exactly. -/
theorem targetGram_submatrix_coercive (a b:ℝ) (ha:-1<a) (hb:-1<b) :
    ∃ κ:ℝ, 0<κ ∧ ∃ N:ℕ, ∀ n≥N, ∀ (m:ℕ) (e:Fin m→Fin (n+1)),
      Function.Injective e → (∀j, 2*(e j).val≤n+1) → ∀ v:Fin m→ℝ,
      κ*(∑ j, (v j)^2) ≤ ∑ i,∑ j, targetGram a b ha hb n (e i) (e j)*v i*v j := by
  -- The zero extension is physical-half supported and preserves the full original form.
  obtain ⟨κ,hκ,N,hbound⟩ := targetGram_uniform_coercive a b ha hb
  refine ⟨κ,hκ,N,fun n hn m e he hp v => ?_⟩
  let w := Function.extend e v (fun _ => (0:ℝ))
  have hw : ∀i:Fin (n+1), n+1<2*i.val → w i=0 := by
    intro i hi
    apply Function.extend_apply'
    rintro ⟨j,hj⟩
    have hh := hp j
    rw [hj] at hh
    omega
  have hh := hbound n hn w hw
  rw [zeroExtension_norm_sq e he v,zeroExtension_quadratic e he (targetGram a b ha hb n) v] at hh
  exact hh

/-- The exact preceding-coordinate Gram blocks used by the actual
Cholesky rows have one uniform positive quadratic gap.
Use: quantitative inverse, row coefficient and Schur normalization
estimates use the same genuine principal matrix as rowCoefficient_inverse.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: the actual before-row coordinate map is injective and lies in
the original physical half whenever its row does. Apply the proved
size-independent original principal-section lower bound. -/
theorem principalGram_uniform_coercive (a b:ℝ) (ha:-1<a) (hb:-1<b) :
    ∃ κ:ℝ, 0<κ ∧ ∃ N:ℕ, ∀ n≥N, ∀ i:Fin (n+1), 2*i.val≤n+1 →
      ∀ v:Fin i.val→ℝ,
      κ*(∑ j, (v j)^2) ≤ ∑ j,∑ k,
        targetGram a b ha hb n (Gram.before i j) (Gram.before i k)*v j*v k := by
  -- Every actual preceding index is physical whenever the original row is physical.
  obtain ⟨κ,hκ,N,hbound⟩ := targetGram_submatrix_coercive a b ha hb
  refine ⟨κ,hκ,N,fun n hn i hi => hbound n hn i.val (Gram.before i) ?_ ?_⟩
  · intro j k hjk
    apply Fin.ext
    exact congrArg (fun l:Fin (n+1) => l.val) hjk
  · intro j
    have hj := j.isLt
    change 2*j.val≤n+1
    omega

end
end jacobi.Comparison
