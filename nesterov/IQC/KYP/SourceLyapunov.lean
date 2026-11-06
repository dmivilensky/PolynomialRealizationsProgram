import nesterov.IQC.KYP.FiniteEnergy
import nesterov.IQC.KYP.SourceMomentum
import nesterov.IQC.KYP.Original
import nesterov.IQC.KYP.PotentialWindow

/-!
Article: Proposition `lyap` in its literal two-position/normalized-gradient
coordinates. The scalar matrix, and every comparison constant, are chosen
before the Hilbert space, objective, minimizer or execution.
-/
namespace nesterov.IQC.KYP
noncomputable section
open scoped BigOperators

variable {β τ h μ L t : ℝ} {hh : h≠0} {M : ℕ}
variable {cert : nesterov.Duality.StrictCertificate ((Momentum.method β τ h hh).symbolPair μ L t) t}

/-- The real coefficient vector with its concrete memory-two index type. -/
def momentumNormalizedCoeff (β τ h μ L : ℝ) (hh : h≠0) (j : Fin 3) : ℝ:=
  (Momentum.method β τ h hh).normalizedCoeff μ L j

/-- A concrete-index leading coefficient lemma avoids changing state indices. -/
theorem momentumNormalizedTop_ne (β τ h μ L : ℝ) (hh : h≠0) (hμL : μ<L) :
    momentumNormalizedCoeff β τ h μ L hh (2 : Fin 3)≠0 :=
  (Momentum.method β τ h hh).normalizedCoeff_top_ne hμL

namespace LyapunovData
variable (D : LyapunovData (Momentum.method β τ h hh) μ L t M cert)

/-- The constructed scalar matrix, reindexed to the source's M+2 convention. -/
def sourceLatentMatrix : Bilinear (Fin (M+2)→ℝ):=
  D.matrix.bilinearComp (selectCLM (Fin.cast (Nat.add_comm 2 M)))
    (selectCLM (Fin.cast (Nat.add_comm 2 M)))

/-- The fixed quadratic matrix in the actual source state X. -/
def sourceMatrix (hμL : μ<L) : Bilinear (Fin (M+2)→ℝ):=
  Real.exp (-2*t) • D.sourceLatentMatrix.bilinearComp
    ((discountWindowCLM (M+2) t).comp
      (sourceCoordinatesEquiv (E:=ℝ) M
        (momentumNormalizedCoeff β τ h μ L hh 0)
        (momentumNormalizedCoeff β τ h μ L hh 1)
        (momentumNormalizedCoeff β τ h μ L hh 2)
        (momentumNormalizedTop_ne β τ h μ L hh hμL)).symm.toContinuousLinearMap)
    ((discountWindowCLM (M+2) t).comp
      (sourceCoordinatesEquiv (E:=ℝ) M
        (momentumNormalizedCoeff β τ h μ L hh 0)
        (momentumNormalizedCoeff β τ h μ L hh 1)
        (momentumNormalizedCoeff β τ h μ L hh 2)
        (momentumNormalizedTop_ne β τ h μ L hh hμL)).symm.toContinuousLinearMap)

end LyapunovData

section State
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- X consists of the preceding and current positions and M successive
normalized gradients; on an actual execution this is the literal source state. -/
def momentumSourceState (β τ h μ L : ℝ) (hh : h≠0) (M : ℕ) (w : ℕ→E) (k : ℕ) : Fin (M+2)→E:=
  sourceCoordinates M (momentumNormalizedCoeff β τ h μ L hh 0)
    (momentumNormalizedCoeff β τ h μ L hh 1)
    (momentumNormalizedCoeff β τ h μ L hh 2) (window (M+2) w k)

end State

def momentumSourceForwardGain (β τ h μ L : ℝ) (hh : h≠0) (M : ℕ) : ℝ:=
  ((M+2:ℕ):ℝ)*(1+|momentumNormalizedCoeff β τ h μ L hh 0|+
    |momentumNormalizedCoeff β τ h μ L hh 1|+
    |momentumNormalizedCoeff β τ h μ L hh 2|)^2

def momentumSourceInverseGain (β τ h μ L : ℝ) (hh : h≠0) (M : ℕ) (hμL : μ<L) : ℝ:=
  ((M+2:ℕ):ℝ)*(sourceInverseBound M
    (momentumNormalizedCoeff β τ h μ L hh 0)
    (momentumNormalizedCoeff β τ h μ L hh 1)
    (momentumNormalizedCoeff β τ h μ L hh 2)
    (momentumNormalizedTop_ne β τ h μ L hh hμL))^2

theorem momentumSourceForwardGain_pos (β τ h μ L : ℝ) (hh : h≠0) (M : ℕ) :
    0<momentumSourceForwardGain β τ h μ L hh M := by
  unfold momentumSourceForwardGain
  have hN : (0:ℝ)<((M+2:ℕ):ℝ):=by positivity
  exact mul_pos hN (sq_pos_of_pos (by positivity))

theorem momentumSourceInverseGain_pos (β τ h μ L : ℝ) (hh : h≠0) (M : ℕ) (hμL : μ<L) :
    0<momentumSourceInverseGain β τ h μ L hh M hμL := by
  unfold momentumSourceInverseGain
  have hi : 0<sourceInverseBound M
      (momentumNormalizedCoeff β τ h μ L hh 0)
      (momentumNormalizedCoeff β τ h μ L hh 1)
      (momentumNormalizedCoeff β τ h μ L hh 2)
      (momentumNormalizedTop_ne β τ h μ L hh hμL):=scalarActionBound_pos _
  exact mul_pos (by positivity) (sq_pos_of_pos hi)

namespace LyapunovData
variable (D : LyapunovData (Momentum.method β τ h hh) μ L t M cert)

def sourceLowerConstant : ℝ:=D.lowerConstant/momentumSourceForwardGain β τ h μ L hh M
def sourceUpperConstant (hμL : μ<L) : ℝ:=D.upperConstant*momentumSourceInverseGain β τ h μ L hh M hμL
def sourceDissipationConstant : ℝ:=D.dissipationConstant/momentumSourceForwardGain β τ h μ L hh M

theorem sourceLowerConstant_pos : 0<D.sourceLowerConstant:=
  div_pos D.lowerConstant_pos (momentumSourceForwardGain_pos _ _ _ _ _ _ _)
theorem sourceUpperConstant_pos (hμL : μ<L) : 0<D.sourceUpperConstant hμL:=
  mul_pos D.upperConstant_pos (momentumSourceInverseGain_pos _ _ _ _ _ _ _ _)
theorem sourceDissipationConstant_pos : 0<D.sourceDissipationConstant:=
  div_pos D.dissipationConstant_pos (momentumSourceForwardGain_pos _ _ _ _ _ _ _)

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The article's quadratic-minus-potential expression in the exact state X. -/
def sourceLyapunov (hμL : μ<L) (ψ : E→ℝ) (w : ℕ→E) (k : ℕ) : ℝ:=
  tensorForm (D.sourceMatrix hμL) (momentumSourceState β τ h μ L hh M w k)
    (momentumSourceState β τ h μ L hh M w k)-
      sourcePotential cert (fun n=>ψ ((Momentum.method β τ h hh).query w n)) k

omit [CompleteSpace E] in
/-- Pulling back the fixed scalar quadratic matrix is exactly the constructed
Lyapunov function, including every discount and potential coefficient. -/
theorem sourceLyapunov_eq (hμL : μ<L) (ψ : E→ℝ) (w : ℕ→E) (k : ℕ) :
    D.sourceLyapunov hμL ψ w k=(Momentum.method β τ h hh).lyapunov cert D.matrix ψ w k := by
  rw [(Momentum.method β τ h hh).lyapunov_form]
  unfold sourceLyapunov sourceMatrix momentumSourceState
  rw [tensorForm_smul,←source_tensor_discount_window]
  unfold sourceLatentMatrix
  rw [tensorForm_select]
  rfl

omit [CompleteSpace E] in
/-- The full source expression is quadratic in X and a linear combination
of exactly its M consecutive queried objective values. -/
theorem sourceLyapunov_form_values (hμL : μ<L) (hM : ∀ n∈cert.lags,n≤M)
    (ψ : E→ℝ) (w : ℕ→E) (k : ℕ) :
    D.sourceLyapunov hμL ψ w k=
      tensorForm (D.sourceMatrix hμL) (momentumSourceState β τ h μ L hh M w k)
        (momentumSourceState β τ h μ L hh M w k)-
          ∑ j∈Finset.range M,potentialCoefficient cert j*ψ ((Momentum.method β τ h hh).query w (k+j)) := by
  unfold sourceLyapunov
  rw [sourcePotential_eq_coefficients_of_bound cert hM]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem momentum_windowEnergy (w : ℕ→E) (k : ℕ) :
    windowEnergy ((Momentum.method β τ h hh).memory+M) w k=finiteEnergy (window (M+2) w k) := by
  change (∑ j : Fin (2+M),‖w (k+j.val)‖^2)=finiteEnergy (window (M+2) w k)
  rw [Nat.add_comm 2 M]
  rfl

omit [CompleteSpace E] in
theorem source_energy_bound (w : ℕ→E) (k : ℕ) :
    finiteEnergy (momentumSourceState β τ h μ L hh M w k)≤
      momentumSourceForwardGain β τ h μ L hh M*windowEnergy ((Momentum.method β τ h hh).memory+M) w k := by
  have he:=source_energy_le M
    (momentumNormalizedCoeff β τ h μ L hh 0)
    (momentumNormalizedCoeff β τ h μ L hh 1)
    (momentumNormalizedCoeff β τ h μ L hh 2) (window (M+2) w k)
  rw [momentum_windowEnergy]
  exact he

omit [CompleteSpace E] in
theorem latent_energy_bound (hμL : μ<L) (w : ℕ→E) (k : ℕ) :
    windowEnergy ((Momentum.method β τ h hh).memory+M) w k≤
      momentumSourceInverseGain β τ h μ L hh M hμL*
        finiteEnergy (momentumSourceState β τ h μ L hh M w k) := by
  have he:=latent_energy_le M
    (momentumNormalizedCoeff β τ h μ L hh 0)
    (momentumNormalizedCoeff β τ h μ L hh 1)
    (momentumNormalizedCoeff β τ h μ L hh 2)
    (momentumNormalizedTop_ne β τ h μ L hh hμL) (window (M+2) w k)
  rw [momentum_windowEnergy]
  exact he

/-- Positive comparison in the literal source state, uniformly over all
Hilbert spaces and all normalized smooth feedbacks. -/
theorem source_comparison (hμ : 0<μ) (hμL : μ<L)
    (hr : middleRadius (Momentum.method β τ h hh) μ L<Real.exp t)
    (hM : ∀ n∈cert.lags,n≤M) {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ)
    (w : ℕ→E)
    (hw : ∀ k,(∑ j : Fin 3,(Momentum.method β τ h hh).normalizedCoeff μ L j • w (k+j))=
      gradient ψ ((Momentum.method β τ h hh).query w k)) (k : ℕ) :
    D.sourceLowerConstant*finiteEnergy (momentumSourceState β τ h μ L hh M w k)≤D.sourceLyapunov hμL ψ w k ∧
      D.sourceLyapunov hμL ψ w k≤D.sourceUpperConstant hμL*finiteEnergy (momentumSourceState β τ h μ L hh M w k) := by
  rw [D.sourceLyapunov_eq]
  have hc:=D.comparison hμ hμL hr hM hψ w hw k
  constructor
  · apply le_trans _ hc.1
    have he:=mul_le_mul_of_nonneg_left (source_energy_bound (μ:=μ) (L:=L) (β:=β) (τ:=τ) (h:=h) (hh:=hh) (M:=M) w k) D.sourceLowerConstant_pos.le
    have hid : D.sourceLowerConstant*momentumSourceForwardGain β τ h μ L hh M=D.lowerConstant:=by
      unfold sourceLowerConstant
      exact div_mul_cancel₀ _ (ne_of_gt (momentumSourceForwardGain_pos _ _ _ _ _ _ _))
    rw [←mul_assoc,hid] at he
    exact he
  · apply hc.2.trans
    have he:=mul_le_mul_of_nonneg_left (latent_energy_bound (μ:=μ) (L:=L) (β:=β) (τ:=τ) (h:=h) (hh:=hh) (M:=M) hμL w k) D.upperConstant_pos.le
    simpa only [sourceUpperConstant,mul_assoc] using he

/-- The strict source dissipation inequality uses the complete X state. -/
theorem source_step (hμL : μ<L) (hM : ∀ n∈cert.lags,n≤M)
    {ψ : E→ℝ} (hψ : polyak.NormalizedSmooth ψ) (w : ℕ→E)
    (hw : ∀ k,(∑ j : Fin 3,(Momentum.method β τ h hh).normalizedCoeff μ L j • w (k+j))=
      gradient ψ ((Momentum.method β τ h hh).query w k)) (k : ℕ) :
    D.sourceLyapunov hμL ψ w (k+1)≤Real.exp (2*t)*D.sourceLyapunov hμL ψ w k-
      D.sourceDissipationConstant*finiteEnergy (momentumSourceState β τ h μ L hh M w k) := by
  rw [D.sourceLyapunov_eq,D.sourceLyapunov_eq]
  apply (D.step hM hψ w hw k).trans
  have he:=mul_le_mul_of_nonneg_left (source_energy_bound (μ:=μ) (L:=L) (β:=β) (τ:=τ) (h:=h) (hh:=hh) (M:=M) w k) D.sourceDissipationConstant_pos.le
  have hid : D.sourceDissipationConstant*momentumSourceForwardGain β τ h μ L hh M=D.dissipationConstant:=by
    unfold sourceDissipationConstant
    exact div_mul_cancel₀ _ (ne_of_gt (momentumSourceForwardGain_pos _ _ _ _ _ _ _))
  rw [←mul_assoc,hid] at he
  linarith

end Hilbert
end LyapunovData
end
end nesterov.IQC.KYP
