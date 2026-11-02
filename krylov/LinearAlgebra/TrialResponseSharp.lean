import krylov.LinearAlgebra.SpectralBudgetDuality
set_option autoImplicit false
/-!
Article: main_krylov, thm:I, exact sharp independent-budget trial responses.
Use: reuse the existing actual symmetric-budget duality to obtain both printed
XRFC response maxima and their comparison, with true attaining operators.
Source: proved symmetric-ball support (Rump03), finite-dimensional unit-sphere
compactness and the existing attained spectral box duality.
-/

namespace krylov.LinearAlgebra
noncomputable section
open scoped BigOperators InnerProductSpace NNReal
variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- The true signed trial response with arbitrary original oblique left actions.
Use: specialize to identity actions for XRFC-D and genuine transported old
flags for step-basis XRFC.
Article: main_krylov, thm:I. -/
def trialObliqueResponse (I : Finset ι) (a : ι → ℝ) (P : ι → E →L[ℝ] E)
    (s : ι → E) (T : ι → E →L[ℝ] E) : E :=
  ∑ i∈I,a i • (P i).adjoint (T i (s i))

/-- The exact step-basis trial-response maximum is the printed attained
unit-direction support maximum, including all zero budgets and coefficients.
Use: no maximizing output vector or perturbation is assumed in the source sharp constant.
Article: main_krylov, thm:I, C_S=max_unit sum omega_l |a_l| norm(Pi_l u).
Proof: put the true signed coefficient into the queried unit vector and use
the proved actual symmetric box-budget duality with adjoint left actions. -/
theorem trial_oblique_response_sharp (I : Finset ι) (omega : ι → ℝ≥0)
    (a : ι → ℝ) (P : ι → E →L[ℝ] E) (s : ι → E) (hs : ∀ i∈I,‖s i‖=1) :
    ∃ C : ℝ≥0,
      IsGreatest ((fun u : E => ∑ i∈I,(omega i : ℝ)*|a i| *‖P i u‖) '' {u : E | ‖u‖=1}) (C : ℝ) ∧
      IsGreatest {z : ℝ | ∃ T : ι → E →L[ℝ] E,
        (∀ i∈I,IsSelfAdjoint (T i) ∧ ‖T i‖≤(omega i : ℝ)) ∧
        z=‖trialObliqueResponse I a P s T‖} (C : ℝ) := by
  obtain ⟨C,hC,hout⟩ := spectral_box_budget_duality I omega (fun i => (P i).adjoint) (fun i => a i • s i)
  have hvalue (u : E) :
      ((∑ i∈I,omega i*‖((P i).adjoint).adjoint u‖₊*‖a i • s i‖₊ : ℝ≥0) : ℝ)=
      ∑ i∈I,(omega i : ℝ)*|a i| *‖P i u‖ := by
    simp only [NNReal.coe_sum,NNReal.coe_mul,coe_nnnorm,ContinuousLinearMap.adjoint_adjoint]
    apply Finset.sum_congr rfl
    intro i hi
    rw [norm_smul,Real.norm_eq_abs,hs i hi,mul_one]
    ring
  have he (T : ι → E →L[ℝ] E) :
      (∑ i∈I,(P i).adjoint (T i (a i • s i)))=trialObliqueResponse I a P s T := by
    simp only [trialObliqueResponse,map_smul]
  refine ⟨C,?_,?_⟩
  · constructor
    · obtain ⟨u,hu,heq⟩ := hC.1
      exact ⟨u,hu,(hvalue u).symm.trans (congrArg (fun c : ℝ≥0 => (c : ℝ)) heq)⟩
    · rintro z ⟨u,hu,rfl⟩
      change (∑ i∈I,(omega i : ℝ)*|a i| *‖P i u‖)≤(C : ℝ)
      rw [← hvalue u]
      exact_mod_cast hC.2 ⟨u,hu,rfl⟩
  · have hset : {z : ℝ | ∃ T∈symmetricBudgetFamily I omega {b | ∀ i∈I,b i≤1},
        z=‖∑ i∈I,(P i).adjoint (T i (a i • s i))‖}=
        {z : ℝ | ∃ T : ι → E →L[ℝ] E,
          (∀ i∈I,IsSelfAdjoint (T i) ∧ ‖T i‖≤(omega i : ℝ)) ∧ z=‖trialObliqueResponse I a P s T‖} := by
      ext z
      simp only [symmetric_box_family_iff,he]
    exact hset ▸ hout

/-- The actual direction-basis trial response has the exact attained sum
constant for all independent symmetric budgets.
Use: sharpness of C_D is proved with actual self-adjoint perturbations.
Article: main_krylov, thm:I, C_D=sum omega_l |a_l|.
Proof: specialize the attained oblique response duality to the identity;
every unit output direction has the same true support sum. -/
theorem trial_direction_response_sharp (I : Finset ι) (omega : ι → ℝ≥0)
    (a : ι → ℝ) (s : ι → E) (hs : ∀ i∈I,‖s i‖=1) :
    IsGreatest {z : ℝ | ∃ T : ι → E →L[ℝ] E,
      (∀ i∈I,IsSelfAdjoint (T i) ∧ ‖T i‖≤(omega i : ℝ)) ∧
      z=‖∑ i∈I,a i • T i (s i)‖} (∑ i∈I,(omega i : ℝ)*|a i|) := by
  obtain ⟨C,hC,hout⟩ := trial_oblique_response_sharp I omega a (fun _ => 1) s hs
  obtain ⟨u,hu,hmax⟩ := hC.1
  change ‖u‖=1 at hu
  have hconst : (∑ i∈I,(omega i : ℝ)*|a i|)=(C : ℝ) := by
    simpa only [one_apply_eq_self,hu,mul_one] using hmax
  rw [← hconst] at hout
  simpa only [trialObliqueResponse,ContinuousLinearMap.adjoint_one,one_apply_eq_self] using hout

omit [CompleteSpace E] [FiniteDimensional ℝ E] [Nontrivial E] in
/-- A common preserved unit direction makes the sharp oblique response at
least the sharp direction-basis sum, including zero coefficients.
Use: the true XRFC old flags all preserve their genuine first column direction.
Article: main_krylov, thm:I, C_S >= C_D.
Proof: evaluate the actual attained directional support at that original unit vector. -/
theorem trial_oblique_constant_ge_direction (I : Finset ι) (omega : ι → ℝ≥0)
    (a : ι → ℝ) (P : ι → E →L[ℝ] E) (C : ℝ)
    (hC : IsGreatest ((fun u : E => ∑ i∈I,(omega i : ℝ)*|a i| *‖P i u‖) '' {u : E | ‖u‖=1}) C)
    (u : E) (hu : ‖u‖=1) (hP : ∀ i∈I,P i u=u) :
    (∑ i∈I,(omega i : ℝ)*|a i|)≤C := by
  have he : (∑ i∈I,(omega i : ℝ)*|a i| *‖P i u‖)=∑ i∈I,(omega i : ℝ)*|a i| := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hP i hi,hu,mul_one]
  simpa only [he] using hC.2 ⟨u,hu,rfl⟩

end
end krylov.LinearAlgebra
