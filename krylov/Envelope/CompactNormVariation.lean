import krylov.Envelope.Geometry
import krylov.Stability.WeightedCompactTaylor

set_option autoImplicit false
/-!
Article: main_krylov, thm:E and cor:lm, genuine compact weighted norm variation.
Use: derive actual uniform quadratic norm-linearization remainders with
the real initial-error weight and explicit inverse-current-error dependence,
using one genuine compact Taylor radius even near exhausted references.
Source: true C-two derivative continuity on compact sets, actual positive
reference weights, the proved uniform weighted Taylor theorem and genuine
Hilbert norm first-order geometry.
-/

namespace krylov.Envelope
noncomputable section
open Set Filter Topology krylov.Stability
variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [ProperSpace X] in
/-- Genuine C-two data on an actual compact reference set have a true uniform derivative bound with every genuine positive continuous reference weight.
Use: Genuine C-two data on an actual compact reference set have a true uniform derivative bound with every genuine positive continuous reference weight.
Article: main_krylov, thm:E and cor:lm, genuine compact weighted norm variation.
Proof: The real derivative norm divided by the actual positive weight is continuous on the genuine compact set and has a true finite bound; apply the actual operator norm estimate. -/
theorem compact_weighted_first_derivative (f : X → E) (e : X → ℝ) (K : Set X) (hK : IsCompact K)
    (hf : ∀ x∈K, ContDiffAt ℝ 2 f x) (he : ContinuousOn e K) (hpos : ∀ x∈K, 0<e x) :
    ∃ M : ℝ, 0≤M ∧ ∀ x∈K, ∀ h : X, ‖fderiv ℝ f x h‖≤M*‖h‖*e x := by
  -- Bound the genuine derivative relative to the actual positive reference weight on the true compact set.
  have hc : ContinuousOn (fun x => ‖fderiv ℝ f x‖/e x) K := by
    apply ContinuousOn.div _ he (fun x hx => (hpos x hx).ne')
    exact fun x hx => ((hf x hx).continuousAt_fderiv (by norm_num)).norm.continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro x hx h
  have hq : ‖fderiv ℝ f x‖/e x≤max C 0 := by
    have hb := hC x hx
    rw [Real.norm_eq_abs] at hb
    exact (le_abs_self _).trans (hb.trans (le_max_left _ _))
  have hd := (div_le_iff₀ (hpos x hx)).mp hq
  calc
    ‖fderiv ℝ f x h‖≤‖fderiv ℝ f x‖*‖h‖ := (fderiv ℝ f x).le_opNorm h
    _ ≤(max C 0*e x)*‖h‖ := mul_le_mul_of_nonneg_right hd (norm_nonneg h)
    _ =max C 0*‖h‖*e x := by ring

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] in
/-- The real Hilbert norm has its genuine first-order variation plus the true norm of an actual vector remainder and an explicit quadratic derivative term.
Use: The real Hilbert norm has its genuine first-order variation plus the true norm of an actual vector remainder and an explicit quadratic derivative term.
Article: main_krylov, thm:E and cor:lm, genuine compact weighted norm variation.
Proof: Split the actual norm difference through its genuine affine vector approximation, use the true reverse triangle inequality and the proved real Hilbert norm linearization estimate. -/
theorem norm_linearization_with_remainder (u d R : E) (hu : 0<‖u‖) :
    |‖u+d+R‖-‖u‖-inner ℝ u d/‖u‖|≤‖R‖+4*‖d‖^2/‖u‖ := by
  -- Separate only the actual affine vector approximation and its genuine remainder before taking norms.
  have he : ‖u+d+R‖-‖u‖-inner ℝ u d/‖u‖=
      (‖u+d+R‖-‖u+d‖)+(‖u+d‖-‖u‖-inner ℝ u d/‖u‖) := by ring
  rw [he]
  have hn : |‖u+d+R‖-‖u+d‖|≤‖R‖ := by
    simpa only [add_sub_cancel_left] using abs_norm_sub_norm_le (u+d+R) (u+d)
  exact (abs_add_le _ _).trans (add_le_add hn (norm_firstOrder_remainder u d hu))

/-- Every genuine compact C-two vector family has its actual common-radius weighted quadratic norm-linearization remainder with the true inverse-current-norm factor.
Use: Every genuine compact C-two vector family has its actual common-radius weighted quadratic norm-linearization remainder with the true inverse-current-norm factor.
Article: main_krylov, thm:E and cor:lm, genuine compact weighted norm variation.
Proof: Derive the actual compact weighted derivative bound and genuine vector Taylor remainder. Apply real norm linearization to that actual first jet and retain its true positive current norm in the denominator; the resulting exact scalar bound has the printed weight times one plus weight over current norm. -/
theorem compact_weighted_norm_variation [CompleteSpace E] (f : X → E) (e : X → ℝ) (K : Set X) (hK : IsCompact K)
    (hf : ∀ x∈K, ContDiffAt ℝ 2 f x) (he : ContinuousOn e K) (hpos : ∀ x∈K, 0<e x) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ → 0<‖f x‖ →
      |‖f (x+h)‖-‖f x‖-inner ℝ (f x) (fderiv ℝ f x h)/‖f x‖|≤
        C*‖h‖^2*e x*(1+e x/‖f x‖) := by
  -- The true C-two locus supplies one actual compact Taylor neighborhood, including references whose current output may vanish.
  let U := interior {x | ContDiffAt ℝ 2 f x}
  have hKU : K⊆U := fun x hx => mem_interior_iff_mem_nhds.mpr ((hf x hx).eventually (by simp))
  have hfU : ContDiffOn ℝ 2 f U := fun x hx =>
    (show ContDiffAt ℝ 2 f x from interior_subset hx).contDiffWithinAt
  obtain ⟨δ,A,hδ,hA,ht⟩ := compact_weighted_taylor f e 2 U K isOpen_interior hK hKU hfU he hpos
  obtain ⟨M,hM,hd⟩ := compact_weighted_first_derivative f e K hK hf he hpos
  refine ⟨δ,A+4*M^2,hδ,by positivity,?_⟩
  intro x hx h hh ha
  let D := fderiv ℝ f x h
  let R := f (x+h)-(f x+D)
  have htwo : taylorPolynomial f 2 x h=f x+D := by
    simp [taylorPolynomial,Finset.sum_range_succ,iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply,D]
  have hR := ht x hx h hh 2 (by omega) le_rfl
  change ‖f (x+h)-taylorPolynomial f 2 x h‖≤_ at hR
  rw [htwo] at hR
  have hD : ‖D‖≤M*‖h‖*e x := hd x hx h
  have hex : 0<e x := hpos x hx
  -- Keep the actual initial-error weight squared until the genuine current-error denominator is restored.
  have hDsq : ‖D‖^2≤M^2*‖h‖^2*(e x)^2 := by
    convert (sq_le_sq₀ (norm_nonneg D) (by positivity : 0≤M*‖h‖*e x)).mpr hD using 1
    ring
  have hfull : f x+D+R=f (x+h) := by dsimp only [R];abel
  have hn := norm_linearization_with_remainder (f x) D R ha
  rw [hfull] at hn
  apply hn.trans
  -- The actual vector remainder and true first-jet norm contribute separate genuine quadratic terms.
  have hfirst : ‖R‖+4*‖D‖^2/‖f x‖≤A*‖h‖^2*e x+4*(M^2*‖h‖^2*(e x)^2)/‖f x‖ :=
    add_le_add hR (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hDsq (by norm_num)) ha.le)
  apply hfirst.trans
  have hr : 0≤e x/‖f x‖ := div_nonneg (hpos x hx).le ha.le
  have hw : 0≤‖h‖^2*e x := mul_nonneg (sq_nonneg _) (hpos x hx).le
  calc
    A*‖h‖^2*e x+4*(M^2*‖h‖^2*(e x)^2)/‖f x‖=
        A*(‖h‖^2*e x)+(4*M^2)*(‖h‖^2*e x)*(e x/‖f x‖) := by ring
    _ ≤(A+4*M^2)*(‖h‖^2*e x)+(A+4*M^2)*(‖h‖^2*e x)*(e x/‖f x‖) :=
      add_le_add (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity : 0≤4*M^2)) hw)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA) hw) hr)
    _ =(A+4*M^2)*‖h‖^2*e x*(1+e x/‖f x‖) := by ring
end
end krylov.Envelope
