import krylov.Correction.UniformCorrectionAlgebra

/-!
Article: main_krylov, thm:UCq, quantitative genuine terminal response geometry.
Use: Reuse the actual full-basis, oblique flag and measured-model algebra
in the uniform second-order RFC expansion without a smallest CG energy.
Source: proved genuine Gram conditioning, exact finite correction identities
and the existing weighted oblique response comparison.
-/

namespace krylov.Correction
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual reconstructed terminal operator splits into true model error, inverse-model error and full-basis Gram error.
Use: Assemble the original actual uniform RFC cubic response.
Article: main_krylov, thm:UCq.
Proof: Expand the genuine operator differences and cancel the actual inverse-dual/dual identity; true linearity telescopes all intermediate terms.
-/
theorem terminal_model_operator_split (X Y P N H L : E →L[ℝ] E) (v : E)
    (hPY : ∀ w : E, P (Y w)=w) :
    P (N (H (Y v)))-L v=
      P ((N-Y.comp (L.comp X)) (H (Y v)))+
      L (X ((H-ContinuousLinearMap.id ℝ E) (Y v)))+
      L ((X.comp Y-ContinuousLinearMap.id ℝ E) v) := by
  simp only [_root_.sub_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,map_sub,hPY]
  abel

/-- True first-order geometric factors, a second-order model error and a second-order fresh-vector error give an explicit cubic terminal-response allowance.
Use: Assemble the original actual uniform RFC cubic response.
Article: main_krylov, thm:UCq.
Proof: Use the exact reconstructed operator split and bound all three real operator actions. The genuine fresh-vector approximation controls the actual incoming norm. The remaining leading-operator action on that second-order vector error is cubic as well.
-/
theorem terminal_model_uniform_cubic (X Y P N H L : E →L[ℝ] E) (v f : E)
    {a b c d e t ε : ℝ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d)
    (he : 0≤e) (hε : 0≤ε) (hε1 : ε≤1)
    (hPY : ∀ w : E, P (Y w)=w)
    (hX : ‖X‖≤2) (hY : ‖Y‖≤2) (hP : ‖P‖≤2) (hH : ‖H‖≤2)
    (hN : ‖N-Y.comp (L.comp X)‖≤c*ε^2)
    (hHerr : ‖H-ContinuousLinearMap.id ℝ E‖≤b*ε)
    (hXY : ‖X.comp Y-ContinuousLinearMap.id ℝ E‖≤a*ε)
    (hL : ‖L‖≤d*ε) (hvf : ‖v-f‖≤e*ε^2) (hf : ‖f‖≤t*ε) :
    ‖-P (N (H (Y v)))+L f‖≤((8*c+d*(4*b+a))*(t+e)+d*e)*ε^3 := by
  have hv : ‖v‖≤(t+e)*ε := by
    have htri := (norm_le_norm_sub_add v f).trans (add_le_add hvf hf)
    have hsq := mul_le_mul_of_nonneg_left hε1 (mul_nonneg he hε)
    nlinarith only [htri,hsq]
  have h₁ : ‖P ((N-Y.comp (L.comp X)) (H (Y v)))‖≤(8*c)*ε^2*‖v‖ := by
    calc
      _ ≤ ‖P‖*(‖N-Y.comp (L.comp X)‖*(‖H‖*(‖Y‖*‖v‖))) := (P.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (((N-Y.comp (L.comp X)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left ((H.le_opNorm _).trans (mul_le_mul_of_nonneg_left (Y.le_opNorm _) (norm_nonneg _)))
            (norm_nonneg _))) (norm_nonneg _))
      _ ≤ 2*((c*ε^2)*(2*(2*‖v‖))) := by gcongr
      _ = _ := by ring
  have h₂ : ‖L (X ((H-ContinuousLinearMap.id ℝ E) (Y v)))‖≤(4*d*b)*ε^2*‖v‖ := by
    calc
      _ ≤ ‖L‖*(‖X‖*(‖H-ContinuousLinearMap.id ℝ E‖*(‖Y‖*‖v‖))) := (L.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left ((X.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (((H-ContinuousLinearMap.id ℝ E).le_opNorm _).trans
            (mul_le_mul_of_nonneg_left (Y.le_opNorm _) (norm_nonneg _))) (norm_nonneg _))) (norm_nonneg _))
      _ ≤ (d*ε)*(2*((b*ε)*(2*‖v‖))) := by gcongr
      _ = _ := by ring
  have h₃ : ‖L ((X.comp Y-ContinuousLinearMap.id ℝ E) v)‖≤(d*a)*ε^2*‖v‖ := by
    calc
      _ ≤ ‖L‖*(‖X.comp Y-ContinuousLinearMap.id ℝ E‖*‖v‖) := (L.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left ((X.comp Y-ContinuousLinearMap.id ℝ E).le_opNorm _) (norm_nonneg _))
      _ ≤ (d*ε)*((a*ε)*‖v‖) := by gcongr
      _ = _ := by ring
  have hoperator : ‖P (N (H (Y v)))-L v‖≤(8*c+d*(4*b+a))*ε^2*‖v‖ := by
    rw [terminal_model_operator_split X Y P N H L v hPY]
    exact ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))).trans
      ((add_le_add (add_le_add h₁ h₂) h₃).trans_eq (by ring))
  have hfresh : ‖L (f-v)‖≤(d*e)*ε^3 := by
    have hvf' : ‖f-v‖≤e*ε^2 := by simpa only [norm_sub_rev] using hvf
    exact ((L.le_opNorm _).trans (mul_le_mul hL hvf' (norm_nonneg _) (by positivity))).trans_eq (by ring)
  have hsplit : -P (N (H (Y v)))+L f= -(P (N (H (Y v)))-L v)+L (f-v) := by rw [map_sub]; abel
  rw [hsplit]
  have htri : ‖-(P (N (H (Y v)))-L v)+L (f-v)‖≤
      (8*c+d*(4*b+a))*ε^2*‖v‖+(d*e)*ε^3 :=
    (norm_add_le _ _).trans (add_le_add (by simpa only [norm_neg] using hoperator) hfresh)
  apply htri.trans
  have hcoeff : 0≤(8*c+d*(4*b+a))*ε^2 := by positivity
  calc
    _ ≤ (8*c+d*(4*b+a))*ε^2*((t+e)*ε)+(d*e)*ε^3 :=
      add_le_add (mul_le_mul_of_nonneg_left hv hcoeff) (le_refl _)
    _ = _ := by ring

end
end krylov.Correction
