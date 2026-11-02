import krylov.Convergence.SlidingFCResidual
import krylov.Convergence.SlidingGramInference
import krylov.XR.LocalCoercivity
import krylov.Methods.ProjectedSearch

/-!
Article: main_krylov, apG:Dunif, uniform observed FC prefix bounds.
Use: derive the staircase residual and genuine model/inverse domains
from actual measured conjugacy and small secant errors, without a
nondegeneracy or minimum-step assumption. Source: the already proved
staircase identity, finite norm bounds and real coefficient coercivity.
-/
namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Secant krylov.XR
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- Actual near-reference conjugate steps have a uniform staircase
residual, even for an arbitrarily short individual line step.
Article: main_krylov, apG:Dunif, FC projected gradient. -/
theorem observable_fc_prefix_residual (g s : ℕ → E) (A : ℕ → E →L[ℝ] E)
    (N : ℕ) (epsilon R : ℝ) (he : 0≤epsilon) (hR : 0≤R)
    (hy : ∀ j<N,g (j+1)-g j=A j (s j))
    (hsym : ∀ j<N,(A j).toLinearMap.IsSymmetric)
    (hA : ∀ j<N,‖A j-ContinuousLinearMap.id ℝ E‖≤epsilon)
    (hline : ∀ j<N,inner ℝ (s j) (g (j+1))=0)
    (hc : ∀ i j,i<j → j<N → inner ℝ (g (i+1)-g i) (s j)=0)
    (hstep : ∀ j,0<j → j<N → ‖s j‖≤2*R) :
    ‖projectedResidual (unitWindow (fun i : Fin N=>s i.val)) (g N)‖≤
      4*epsilon*R*(N:ℝ)*Real.sqrt N := by
  have hdiff (i j : ℕ) (hij : i<j) (hj : j<N) : ‖A j-A i‖≤2*epsilon := by
    have hh := norm_sub_le_norm_sub_add_norm_sub (A j) (ContinuousLinearMap.id ℝ E) (A i)
    rw [norm_sub_rev (ContinuousLinearMap.id ℝ E) (A i)] at hh
    exact hh.trans (by linarith only [hA i (by omega),hA j hj])
  have hbound (i : Fin N) :
      |coordinates (unitWindow (fun i : Fin N=>s i.val)) (g N) i|≤4*epsilon*R*N := by
    have hh := conjugate_staircase_coordinate_bound g s A N (by positivity) (by positivity)
      hy hsym hline hc hdiff hstep i.isLt
    have hN : ((N-1:ℕ):ℝ)≤N := by exact_mod_cast Nat.sub_le N 1
    have hmul := mul_le_mul_of_nonneg_right hN (by positivity : 0≤(2*epsilon)*(2*R))
    exact hh.trans (by nlinarith only [hmul])
  exact (coordinate_norm_le_sqrt_card _ (by positivity) hbound).trans_eq (by ring)

/-- The real identity coefficient form is precisely the Euclidean
squared norm, also for an empty stored window. Article: apG:Dunif. -/
theorem observable_identity_form (c : Fin p → ℝ) :
    c ⬝ᵥ ((1 : Matrix (Fin p) (Fin p) ℝ)*ᵥc)=‖WithLp.toLp 2 c‖^2 := by
  rw [one_mulVec,←real_inner_self_eq_norm_sq,EuclideanSpace.inner_toLp_toLp,star_trivial]

/-- Primitive actual unit secants and triangular measured conjugacy
derive all old FC inverse domains uniformly over the whole prefix.
Article: main_krylov, apG:Dunif, no assumed independence. -/
theorem observable_fc_coefficient_domains (s y : Fin p → E) (hs : ∀ i,‖s i‖=1)
    (epsilon : ℝ) (he : 0≤epsilon) (hy : ∀ i,‖y i-s i‖≤epsilon)
    (hc : ∀ i j,i<j → inner ℝ (y i) (s j)=0) (hsmall : (p:ℝ)*epsilon≤1/8) :
    (∀ c : Fin p → ℝ,(7/8:ℝ)*‖WithLp.toLp 2 c‖^2≤c ⬝ᵥ (crossGram s s*ᵥc)) ∧
      (latest (crossGram s y)).PosDef ∧ IsUnit (crossGram y s).det ∧
      ‖(latest (crossGram s y))⁻¹‖≤4/3 ∧ ‖(crossGram y s)⁻¹‖≤4/3 := by
  have hgram := conjugate_window_gram_bound s y hs he hy hc
  have hsym : (ContinuousLinearMap.id ℝ E).toLinearMap.IsSymmetric := by intro v w;rfl
  have hlatest : ‖latest (crossGram s y)-crossGram s s‖≤p*epsilon := by
    simpa only [localReferenceGram,ContinuousLinearMap.id_apply] using
      local_latest_error_norm (ContinuousLinearMap.id ℝ E) hsym s y hs he hy
  have hsolve : ‖crossGram y s-crossGram s s‖≤p*epsilon := by
    simpa only [localReferenceGram,ContinuousLinearMap.id_apply] using
      local_conjugacy_error_norm (ContinuousLinearMap.id ℝ E) s y hs he hy
  have hsum (M : Matrix (Fin p) (Fin p) ℝ) (hm : ‖M-crossGram s s‖≤p*epsilon) :
      ‖M-1‖≤2*p*epsilon := by
    have hh := norm_add_le (M-crossGram s s) (crossGram s s-1)
    rw [sub_add_sub_cancel] at hh
    exact hh.trans (by linarith only [hm,hgram])
  have hId (c : Fin p → ℝ) : 1*‖WithLp.toLp 2 c‖^2≤c ⬝ᵥ ((1:Matrix (Fin p) (Fin p) ℝ)*ᵥc) := by
    rw [observable_identity_form,one_mul]
  have hco (M : Matrix (Fin p) (Fin p) ℝ) (hm : ‖M-1‖≤2*p*epsilon) (c : Fin p → ℝ) :
      (3/4:ℝ)*‖WithLp.toLp 2 c‖^2≤c ⬝ᵥ (M*ᵥc) := by
    have hh := coefficient_coercivity_of_error M 1 1 (2*p*epsilon) hId hm c
    nlinarith only [hh,mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖WithLp.toLp 2 c‖)]
  have hT := coefficient_inverse_of_coercivity _ (3/4) (by norm_num) (hco _ (hsum _ hlatest))
  have hC := coefficient_inverse_of_coercivity _ (3/4) (by norm_num) (hco _ (hsum _ hsolve))
  refine ⟨?_,?_,hC.1,by norm_num at hT;exact hT.2,by norm_num at hC;exact hC.2⟩
  · intro c
    have hh := coefficient_coercivity_of_error (crossGram s s) 1 1 (p*epsilon) hId hgram c
    nlinarith only [hh,mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖WithLp.toLp 2 c‖)]
  · apply Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_iff_isSymm.mpr (latest_isSymm _))
    intro c hc0
    have hn : 0<‖WithLp.toLp 2 c‖^2 := pow_pos (norm_pos_iff.mpr
      (fun hz=>hc0 ((WithLp.toLp_injective 2) hz))) _
    simpa only [star_trivial] using (mul_pos (by norm_num : (0:ℝ)<3/4) hn).trans_le
      (hco _ (hsum _ hlatest) c)

end
end krylov.Convergence
