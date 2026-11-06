import nesterov.Rates.Limit

/-! The genuine all-objective rates respect inclusion of the original smooth
strongly convex classes, before any spectral characterization is used. -/
namespace nesterov.Rates
noncomputable section
open Set Filter
open scoped Topology

 theorem class_weaken {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ μ' L : ℝ} {f : E→ℝ} (hf : polyak.CenteredSmoothStronglyConvex μ' L f)
    (hμ : 0<μ) (h : μ≤μ') : polyak.CenteredSmoothStronglyConvex μ L f where
  mu_pos := hμ
  mu_lt_L := h.trans_lt hf.mu_lt_L
  differentiable := hf.differentiable
  tangent_lower x y := by
    have hh := mul_le_mul_of_nonneg_right (show μ/2≤μ'/2 by linarith) (sq_nonneg ‖y-x‖)
    linarith [hf.tangent_lower x y]
  grad_lipschitz := hf.grad_lipschitz
  value_zero := hf.value_zero
  gradient_zero := hf.gradient_zero

 theorem envelope_antitone_mu (M : StationaryMethod) {μ μ' L : ℝ}
    (hμ : 0<μ) (h : μ≤μ') (n : ℕ) : envelope M μ' L n≤envelope M μ L n := by
  apply csSup_le (insert_nonempty _ _)
  intro x hx
  rcases hx with rfl | ⟨r,hr,rfl⟩
  · exact envelope_nonneg M μ L n
  · let r' : HilbertRun M μ L := {r with admissible:=class_weaken r.admissible hμ h}
    apply le_csSup (ratios_bddAbove M μ L n)
    exact Or.inr ⟨r',hr,rfl⟩

 theorem rate_antitone_mu (M : StationaryMethod) {μ μ' L : ℝ}
    (hμ : 0<μ) (h : μ≤μ') (hμ'L : μ'<L) : rate M μ' L≤rate M μ L := by
  apply le_of_tendsto_of_tendsto (tendsto_envelope_root M (hμ.trans_le h) hμ'L)
    (tendsto_envelope_root M hμ (h.trans_lt hμ'L))
  exact Eventually.of_forall fun n=>Real.rpow_le_rpow (envelope_nonneg M μ' L n)
    (envelope_antitone_mu M hμ h n) (by positivity)

end
end nesterov.Rates
