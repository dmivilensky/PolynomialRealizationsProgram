import nesterov.Stationary.FiniteSpan

/-!
Article: Definition `def:rate`, Lemma `lem:envelope`, Remark `rem:uniform-smoothness`.
Use: the small-carrier real supremum controls actual trajectories in every
universe. A finite prefix is compressed into a genuine Euclidean execution
before invoking the supremum. No carrier-size assumption enters the bounds.
-/
namespace nesterov
noncomputable section
open scoped BigOperators InnerProductSpace

namespace StationaryMethod

variable (M : StationaryMethod)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A trajectory in any universe admits an exact finite-prefix realization on
an ordinary finite-dimensional Euclidean space. Both actual curvature constants
and all prefix state norms are retained. -/
theorem exists_euclidean_prefix {μ L : ℝ} {f : E → ℝ}
    (hf : polyak.CenteredSmoothStronglyConvex μ L f) {w : ℕ → E}
    (hrec : M.IsTrajectory (gradient f) w) (n : ℕ) :
    ∃ s : Rates.HilbertRun M μ L, FiniteDimensional ℝ s.Carrier ∧
      ∃ J : s.Carrier →ₗᵢ[ℝ] E,
        (∀ i < n+M.memory, J (s.w i)=w i) ∧
        ∀ k ≤ n, s.stateNorm k=M.stateNorm w k := by
  let a : Fin (n+M.memory) → E := fun i => w i
  let V : Submodule ℝ E := Submodule.span ℝ (Set.range a)
  have : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range a)
  let e := (stdOrthonormalBasis ℝ V).repr
  let d := Module.finrank ℝ V
  let J : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] E :=
    V.subtypeₗᵢ.comp e.symm.toLinearIsometry
  let P := polyak.embeddingProjection J
  let v : ℕ → EuclideanSpace ℝ (Fin d) := fun k => P (w k)
  let F : EuclideanSpace ℝ (Fin d) → ℝ := fun x => f (J x)
  have hF : polyak.CenteredSmoothStronglyConvex μ L F := Functions.centered_restrict hf J
  have hJ (i : ℕ) (hi : i<n+M.memory) : J (v i)=w i := by
    let x : V := ⟨w i,Submodule.subset_span ⟨⟨i,hi⟩,rfl⟩⟩
    have hx : J (e x)=w i := by
      change ((e.symm (e x) : V) : E)=w i
      rw [e.symm_apply_apply]
    dsimp [v,P]
    rw [← hx,polyak.embeddingProjection_embed]
  have hqueryJ (k : ℕ) (hk : k<n) : J (M.query v k)=M.query w k := by
    simp only [query,map_sum,map_smul]
    apply Finset.sum_congr rfl
    intro j _
    rw [hJ (k+j) (by omega)]
  have hv : ∀ k<n, ∑ j : Fin (M.memory+1), M.recurrenceCoeff j • v (k+j)=
      gradient F (M.query v k) := by
    intro k hk
    calc
      _ = P (∑ j : Fin (M.memory+1),M.recurrenceCoeff j • w (k+j)) := by
        simp only [v,map_sum,map_smul]
      _ = P (gradient f (M.query w k)) := congrArg P (hrec k)
      _ = gradient F (M.query v k) := by
        rw [(Functions.hasGradientAt_restrict J hf.differentiable _).gradient,hqueryJ k hk]
  let initial : Fin M.memory → EuclideanSpace ℝ (Fin d) := fun j => v j
  let z := M.run (gradient F) initial
  have hz : ∀ i<n+M.memory,z i=v i := M.run_eq_of_prefix n hv
  let s : Rates.HilbertRun M μ L :=
    ⟨EuclideanSpace ℝ (Fin d),F,hF,z,M.run_isTrajectory _ initial⟩
  refine ⟨s,inferInstance,J,?_,?_⟩
  · intro i hi
    change J (z i)=w i
    rw [hz _ hi,hJ _ hi]
  · intro k hk
    change M.stateNorm z k=M.stateNorm w k
    unfold stateNorm
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have hi : k+j<n+M.memory := by omega
    rw [hz _ hi,← J.norm_map,hJ _ hi]

/-- The literal uniform envelope controls actual centered trajectories in any
real Hilbert space, independently of the carrier's universe. -/
theorem actual_stateNorm_le_envelope_all_hilbert {μ L : ℝ} {f : E → ℝ}
    (hf : polyak.CenteredSmoothStronglyConvex μ L f) {w : ℕ → E}
    (hw : M.IsTrajectory (gradient f) w) (k n : ℕ) :
    M.stateNorm w (k+n) ≤ Rates.envelope M μ L n*M.stateNorm w k := by
  obtain ⟨s,_,_,_,hs⟩ := M.exists_euclidean_prefix hf (hw.shift M k) n
  have h := Rates.stateNorm_le_envelope s n
  rw [hs n le_rfl,hs 0 (Nat.zero_le _)] at h
  simpa only [M.stateNorm_shift,Nat.add_zero] using h

/-- Centering at the actual minimizer transports the genuine objective class
and the genuine recurrence without changing the physical error trajectory. -/
theorem actual_error_stateNorm_le_envelope {μ L : ℝ} {f : E → ℝ}
    (hf : polyak.SmoothStronglyConvex μ L f) (xstar : E)
    (hmin : ∀ x, f xstar≤f x) {w : ℕ → E} (hw : M.IsTrajectory (gradient f) w)
    (k n : ℕ) :
    M.stateNorm (fun i => w i-xstar) (k+n) ≤
      Rates.envelope M μ L n*M.stateNorm (fun i => w i-xstar) k := by
  let F := polyak.centerObjective f xstar
  have hF : polyak.CenteredSmoothStronglyConvex μ L F := by
    refine ⟨hf.centerObjective xstar,?_,?_⟩
    · simp [F,polyak.centerObjective]
    · rw [(polyak.hasGradientAt_centerObjective hf.differentiable xstar 0).gradient]
      simpa using (hf.minimizer_iff xstar).mp hmin
  have hrec : M.IsTrajectory (gradient F) (fun i => w i-xstar) := by
    intro i
    rw [(polyak.hasGradientAt_centerObjective hf.differentiable xstar _).gradient]
    exact hw.center M xstar i
  exact M.actual_stateNorm_le_envelope_all_hilbert hF hrec k n

end StationaryMethod
end
end nesterov
