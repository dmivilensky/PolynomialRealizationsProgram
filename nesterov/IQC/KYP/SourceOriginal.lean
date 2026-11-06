import nesterov.IQC.KYP.SourceLyapunov

/-! Proposition `lyap` for the actual original objective and momentum iterates. -/
namespace nesterov.IQC.KYP
noncomputable section
open scoped BigOperators
variable {β τ h μ L t : ℝ} {hh : h≠0} {M : ℕ}
variable {cert : nesterov.Duality.StrictCertificate ((Momentum.method β τ h hh).symbolPair μ L t) t}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private theorem centered_minimizer {f : E→ℝ} (hf : polyak.SmoothStronglyConvex μ L f)
    (xstar : E) (hmin : ∀ x,f xstar≤f x) :
    polyak.CenteredSmoothStronglyConvex μ L (polyak.centerObjective f xstar) := by
  refine ⟨hf.centerObjective xstar,by simp [polyak.centerObjective],?_⟩
  rw [(polyak.hasGradientAt_centerObjective hf.differentiable xstar 0).gradient]
  simpa using (hf.minimizer_iff xstar).mp hmin

/-- The literal original-objective state consists of actual position errors
and actual normalized gradient evaluations at the corresponding queries. -/
theorem momentumSourceState_original {f : E→ℝ} (hf : Differentiable ℝ f)
    (xstar : E) (w : ℕ→E) (hw : (Momentum.method β τ h hh).IsTrajectory (gradient f) w)
    (M k : ℕ) :
    momentumSourceState β τ h μ L hh M (fun j=>w j-xstar) k=
      fun i : Fin (M+2)=>if i.val=0 then w k-xstar else if i.val=1 then w (k+1)-xstar else
        gradient (polyak.normalizeFunction μ L (polyak.centerObjective f xstar))
          ((Momentum.method β τ h hh).query w (k+(i.val-2))-xstar) := by
  have hc:=hw.centerObjective (Momentum.method β τ h hh) hf xstar
  have hd : Differentiable ℝ (polyak.centerObjective f xstar):=
    fun x=>(polyak.hasGradientAt_centerObjective hf xstar x).differentiableAt
  have he:=momentum_sourceCoordinates_actual (μ:=μ) (L:=L) hh
    hd hc M k
  simp only [StationaryMethod.query_sub_const] at he
  convert he using 1
  unfold momentumSourceState momentumNormalizedCoeff
  congr 2

namespace LyapunovData
variable (D : LyapunovData (Momentum.method β τ h hh) μ L t M cert)

/-- The comparison conclusion of Proposition lyap, with the actual objective,
actual minimizer and the full original momentum trajectory. -/
theorem original_source_comparison (hμ : 0<μ) (hμL : μ<L)
    (hr : middleRadius (Momentum.method β τ h hh) μ L<Real.exp t)
    (hM : ∀ n∈cert.lags,n≤M) {f : E→ℝ}
    (hf : polyak.SmoothStronglyConvex μ L f) (xstar : E) (hmin : ∀ x,f xstar≤f x)
    (w : ℕ→E) (hw : (Momentum.method β τ h hh).IsTrajectory (gradient f) w) (k : ℕ) :
    D.sourceLowerConstant*finiteEnergy (momentumSourceState β τ h μ L hh M (fun j=>w j-xstar) k)≤
      D.sourceLyapunov hμL (polyak.normalizeFunction μ L (polyak.centerObjective f xstar)) (fun j=>w j-xstar) k ∧
    D.sourceLyapunov hμL (polyak.normalizeFunction μ L (polyak.centerObjective f xstar)) (fun j=>w j-xstar) k≤
      D.sourceUpperConstant hμL*finiteEnergy (momentumSourceState β τ h μ L hh M (fun j=>w j-xstar) k) := by
  have hc:=centered_minimizer hf xstar hmin
  exact D.source_comparison hμ hμL hr hM hc.normalize (fun j=>w j-xstar)
    ((hw.centerObjective (Momentum.method β τ h hh) hf.differentiable xstar).normalized
      (Momentum.method β τ h hh) hc.differentiable) k

/-- The strict dissipation conclusion of Proposition lyap on the actual
uncentered objective, without supplied gradients or independent samples. -/
theorem original_source_step (hμL : μ<L) (hM : ∀ n∈cert.lags,n≤M)
    {f : E→ℝ} (hf : polyak.SmoothStronglyConvex μ L f)
    (xstar : E) (hmin : ∀ x,f xstar≤f x)
    (w : ℕ→E) (hw : (Momentum.method β τ h hh).IsTrajectory (gradient f) w) (k : ℕ) :
    D.sourceLyapunov hμL (polyak.normalizeFunction μ L (polyak.centerObjective f xstar)) (fun j=>w j-xstar) (k+1)≤
      Real.exp (2*t)*D.sourceLyapunov hμL (polyak.normalizeFunction μ L (polyak.centerObjective f xstar)) (fun j=>w j-xstar) k-
        D.sourceDissipationConstant*finiteEnergy (momentumSourceState β τ h μ L hh M (fun j=>w j-xstar) k) := by
  have hc:=centered_minimizer hf xstar hmin
  exact D.source_step hμL hM hc.normalize (fun j=>w j-xstar)
    ((hw.centerObjective (Momentum.method β τ h hh) hf.differentiable xstar).normalized
      (Momentum.method β τ h hh) hc.differentiable) k

/-- The exact from-rest iterate estimate printed in Proposition lyap. Its
constant depends only on the method, class and finite certificate. -/
theorem original_iterate_norm_bound (hμ : 0<μ) (hμL : μ<L)
    (hr : middleRadius (Momentum.method β τ h hh) μ L<Real.exp t) (hr1 : Real.exp t≤1)
    (hM : ∀ n∈cert.lags,n≤M) {f : E→ℝ}
    (hf : polyak.SmoothStronglyConvex μ L f) (xstar : E) (hmin : ∀ x,f xstar≤f x)
    (x0 : E) (n : ℕ) :
    ‖Momentum.iterate (gradient f) β τ h x0 n-xstar‖≤D.restConstant*(Real.exp t)^n*‖x0-xstar‖ := by
  have hi : ∀ j : Fin (Momentum.method β τ h hh).memory,
      Momentum.history (gradient f) β τ h x0 x0 j.val=x0 := by
    intro j
    change Fin 2 at j
    fin_cases j <;> rfl
  have hn:=D.original_fromRest_norm_bound hμ hμL hr hM hf xstar hmin
    (Momentum.history (gradient f) β τ h x0 x0)
    (Momentum.history_isTrajectory (gradient f) β τ h hh x0 x0) x0 hi (n+1)
  change ‖Momentum.iterate (gradient f) β τ h x0 n-xstar‖≤
    D.restConstant*(Real.exp t)^(n+1)*‖x0-xstar‖ at hn
  have hp : (Real.exp t)^(n+1)≤(Real.exp t)^n := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg (Real.exp_pos t).le n) hr1
  have hm:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp D.restConstant_pos.le) (norm_nonneg (x0-xstar))
  exact hn.trans hm

omit [CompleteSpace E] in
/-- With the lag-one normalization, the original-objective Lyapunov form
has exactly the quadratic-plus-function correction in the article. -/
theorem original_source_lagOne_form (hμL : μ<L)
    (hlags : cert.lags={1}) (hα : cert.α 1=Real.exp t) (hβ : cert.β 1=0)
    (f : E→ℝ) (xstar : E) (w : ℕ→E) (k : ℕ) :
    D.sourceLyapunov hμL (polyak.normalizeFunction μ L (polyak.centerObjective f xstar)) (fun j=>w j-xstar) k=
      tensorForm (D.sourceMatrix hμL) (momentumSourceState β τ h μ L hh M (fun j=>w j-xstar) k)
        (momentumSourceState β τ h μ L hh M (fun j=>w j-xstar) k)+
          4/(L-μ)*(f ((Momentum.method β τ h hh).query w k)-f xstar-
            (L+μ)/4*‖(Momentum.method β τ h hh).query w k-xstar‖^2) := by
  unfold sourceLyapunov
  rw [sub_eq_add_neg,lagOne_original_correction cert hlags hα hβ]

end LyapunovData
end
end nesterov.IQC.KYP
