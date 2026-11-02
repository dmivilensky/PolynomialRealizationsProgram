import krylov.LinearAlgebra.SpectralBudgetDuality
set_option autoImplicit false
/-!
Article: main_krylov, prop:launch(a), exact evaluated-launch support.
Use: optimize the genuine compression-times-launch error under independent
symmetric spectral budgets, with attained upper and lower comparisons.
Source: the existing attained symmetric box-budget duality, Cauchy--Schwarz
and the actual common preserved first reference direction.
-/

namespace krylov.LinearAlgebra
noncomputable section
open scoped BigOperators InnerProductSpace NNReal
variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- The original evaluated-launch first response with its genuine left
compression and compressed actual launch vector.
Use: specialize to the true orthogonal CG prefix projections.
Article: main_krylov, prop:launch(a). -/
def evaluatedLaunchResponse (I : Finset ι) (P : ι → E →L[ℝ] E) (e : E)
    (T : ι → E →L[ℝ] E) : E := ∑ i∈I,(P i).adjoint (T i (P i e))

/-- The actual compression-times-launch response has exactly the attained
unit-direction support sum, also for zero launches or zero budgets.
Use: the source evaluated-launch constant is a true uncertainty maximum.
Article: main_krylov, prop:launch(a), C_EV=max_unit sum omega_l norm(P_l u) norm(P_l e).
Proof: specialize the existing exact symmetric box-budget duality to the
actual adjoint left compressions and actual compressed launch vectors. -/
theorem evaluated_launch_response_sharp (I : Finset ι) (omega : ι → ℝ≥0)
    (P : ι → E →L[ℝ] E) (e : E) :
    ∃ C : ℝ≥0,
      IsGreatest ((fun u : E => ∑ i∈I,(omega i : ℝ)*‖P i u‖*‖P i e‖) '' {u : E | ‖u‖=1}) (C : ℝ) ∧
      IsGreatest {z : ℝ | ∃ T : ι → E →L[ℝ] E,
        (∀ i∈I,IsSelfAdjoint (T i) ∧ ‖T i‖≤(omega i : ℝ)) ∧
        z=‖evaluatedLaunchResponse I P e T‖} (C : ℝ) := by
  obtain ⟨C,hC,hout⟩ := spectral_box_budget_duality I omega (fun i => (P i).adjoint) (fun i => P i e)
  refine ⟨C,?_,?_⟩
  · constructor
    · obtain ⟨u,hu,he⟩ := hC.1
      refine ⟨u,hu,?_⟩
      simpa only [NNReal.coe_sum,NNReal.coe_mul,coe_nnnorm,ContinuousLinearMap.adjoint_adjoint]
        using congrArg (fun c : ℝ≥0 => (c : ℝ)) he
    · rintro z ⟨u,hu,rfl⟩
      have h := hC.2 ⟨u,hu,rfl⟩
      simp only [ContinuousLinearMap.adjoint_adjoint] at h
      have hreal : ((∑ i∈I,omega i*‖P i u‖₊*‖P i e‖₊ : ℝ≥0) : ℝ)≤(C : ℝ) := by
        exact_mod_cast h
      simpa only [NNReal.coe_sum,NNReal.coe_mul,coe_nnnorm] using hreal
  · have hset : {z : ℝ | ∃ T∈symmetricBudgetFamily I omega {b | ∀ i∈I,b i≤1},
        z=‖∑ i∈I,(P i).adjoint (T i (P i e))‖}=
        {z : ℝ | ∃ T : ι → E →L[ℝ] E,
          (∀ i∈I,IsSelfAdjoint (T i) ∧ ‖T i‖≤(omega i : ℝ)) ∧
            z=‖evaluatedLaunchResponse I P e T‖} := by
      ext z
      simp only [symmetric_box_family_iff,evaluatedLaunchResponse]
    exact hset ▸ hout

omit [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
/-- Genuine contractive compressions bound the true evaluated-launch
maximum by the total budget times the actual launch norm.
Use: gives the original root-sum-square trial-error upper comparison.
Article: main_krylov, prop:launch(a).
Proof: evaluate at the actual maximizing unit direction and use both true
contraction inequalities in every nonnegative weighted support term. -/
theorem evaluated_launch_support_upper (I : Finset ι) (omega : ι → ℝ≥0)
    (P : ι → E →L[ℝ] E) (e : E) (C : ℝ)
    (hC : IsGreatest ((fun u : E => ∑ i∈I,(omega i : ℝ)*‖P i u‖*‖P i e‖) '' {u : E | ‖u‖=1}) C)
    (hP : ∀ i∈I,∀ v,‖P i v‖≤‖v‖) : C≤(∑ i∈I,(omega i : ℝ))*‖e‖ := by
  obtain ⟨u,hu,he⟩ := hC.1
  rw [← he,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hpu : ‖P i u‖≤1 := (hP i hi u).trans_eq hu
  calc
    _ ≤ (omega i : ℝ)*1*‖P i e‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpu (omega i).coe_nonneg) (norm_nonneg _)
    _ ≤ (omega i : ℝ)*1*‖e‖ :=
      mul_le_mul_of_nonneg_left (hP i hi e) (by positivity)
    _ = _ := by rw [mul_one]

omit [FiniteDimensional ℝ E] [Nontrivial E] in
/-- A genuine common preserved unit direction gives the original
evaluated-launch lower comparison from its actual launch component.
Use: the first true CG unit step is preserved by every old CG projection.
Article: main_krylov, prop:launch(a).
Proof: test the exact support at that real direction; self-adjointness and
preservation identify its pairing with every compressed launch, whose norm
dominates the absolute pairing by Cauchy--Schwarz. -/
theorem evaluated_launch_support_lower (I : Finset ι) (omega : ι → ℝ≥0)
    (P : ι → E →L[ℝ] E) (e : E) (C : ℝ)
    (hC : IsGreatest ((fun u : E => ∑ i∈I,(omega i : ℝ)*‖P i u‖*‖P i e‖) '' {u : E | ‖u‖=1}) C)
    (u : E) (hu : ‖u‖=1) (hself : ∀ i∈I,(P i).adjoint=P i)
    (hkeep : ∀ i∈I,P i u=u) : (∑ i∈I,(omega i : ℝ))*|inner ℝ u e|≤C := by
  apply le_trans _ (hC.2 ⟨u,hu,rfl⟩)
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have he : inner ℝ u (P i e)=inner ℝ u e := by
    rw [← ContinuousLinearMap.adjoint_inner_left,hself i hi,hkeep i hi]
  have hb : |inner ℝ u e|≤‖P i e‖ := by
    have h := abs_real_inner_le_norm u (P i e)
    rwa [he,hu,one_mul] at h
  rw [hkeep i hi,hu,mul_one]
  exact mul_le_mul_of_nonneg_left hb (omega i).coe_nonneg

end
end krylov.LinearAlgebra
