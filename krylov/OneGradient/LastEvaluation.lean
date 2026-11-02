import krylov.OneGradient.CompletionCG
import krylov.OneGradient.OutputUncertainty
set_option autoImplicit false
/-!
Article: main_krylov, thm:exact, last evaluated point.
Use: derive the exact physical energy decomposition at the last evaluated point
and the genuine positive CG denominator used in the arbitrary-method lower bound.
Source: actual CG conjugacy and Euclidean Pythagoras after the true metric root.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Secant
variable {m : ℕ}

/-- Actual old Krylov vectors are conjugate to the true next CG direction.
Use: remove the old-flag component from the last-step minimax lower bound.
Article: main_krylov, thm:exact.
Proof: expand the actual direction basis of the Krylov flag and extend the
proved pairwise CG conjugacy by linearity. -/
theorem old_flag_conjugate (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin m)) (N : ℕ) (hN : N<referenceAtomCount A hA g)
    (v : EuclideanSpace ℝ (Fin m)) (hv : v∈CG.krylovSpace (cgOperator A) g N) :
    inner ℝ v (cgOperator A (CG.direction (cgOperator A) g N))=0 := by
  have hp := cgOperator_positive A hA
  have hi := CG.invariant _ hp.1 hp.2 g N (fun j hj => cg_nonstagnation A hA g j (hj.trans hN))
  rw [CG.krylovSpace_eq_span_directions _ _ N (fun i hi' => (hi.lines_pos i hi').ne')] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,hi',rfl⟩ := hx
    exact hi.conjugate i N hi' le_rfl
  | zero => exact inner_zero_left _
  | add x y _ _ hx hy => rw [inner_add_left,hx,hy,add_zero]
  | smul c x _ hx => rw [real_inner_smul_left,hx,mul_zero]

/-- The actual last reference error equals minus the actual canonical last step.
Use: justify the source's denominator from the original terminating CG run.
Article: main_krylov, thm:exact.
Proof: apply the proved canonical CG error update at genuine exhaustion. -/
theorem last_reference_error (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin m)) (N : ℕ) (hN : referenceAtomCount A hA g=N+1) :
    cgCanonicalError A g N= -CG.length (cgOperator A) g N •
      cgOperator (metricRoot A) (CG.direction (cgOperator A) g N) := by
  have ht : cgCanonicalError A g (N+1)=0 := by
    simp only [cgCanonicalError,← hN,cg_terminates A hA g,map_zero]
  rw [cgCanonicalError_succ A hA,canonicalCGStep,cgStep,map_smul] at ht
  change cgCanonicalError A g N+CG.length (cgOperator A) g N •
    cgOperator (metricRoot A) (CG.direction (cgOperator A) g N)=0 at ht
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left ht

/-- The genuine last reference denominator is positive and has the printed
line-length times canonical-direction norm.
Use: no division by an assumed reference error enters the physical minimax theorem.
Article: main_krylov, thm:exact.
Proof: the true last residual is nonzero, so its actual CG line and curvature
are positive. The metric search pairing makes its canonical direction nonzero. -/
theorem last_reference_denominator (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin m)) (N : ℕ) (hN : referenceAtomCount A hA g=N+1) :
    0<‖cgCanonicalError A g N‖ ∧
      ‖cgCanonicalError A g N‖=CG.length (cgOperator A) g N*
        ‖cgOperator (metricRoot A) (CG.direction (cgOperator A) g N)‖ := by
  have hp := cgOperator_positive A hA
  have hlt : N<referenceAtomCount A hA g := by omega
  have hi := CG.invariant _ hp.1 hp.2 g N (fun j hj => cg_nonstagnation A hA g j (hj.trans hlt))
  obtain ⟨hd,ha,_⟩ := CG.invariant_line_pos _ hp.2 g N hi (cg_nonstagnation A hA g N hlt)
  have hmetric : inner ℝ (CG.direction (cgOperator A) g N)
      (cgOperator A (CG.direction (cgOperator A) g N))=
      ‖cgOperator (metricRoot A) (CG.direction (cgOperator A) g N)‖^2 := by
    rw [canonical_search_pairing A hA,canonical_reference_action A hA,real_inner_self_eq_norm_sq]
    rfl
  have hnorm : 0<‖cgOperator (metricRoot A) (CG.direction (cgOperator A) g N)‖ := by
    have hh := hp.2 _ hd
    rw [hmetric] at hh
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm (sq_pos_iff.mp hh))
  have he : ‖cgCanonicalError A g N‖=CG.length (cgOperator A) g N*
      ‖cgOperator (metricRoot A) (CG.direction (cgOperator A) g N)‖ := by
    rw [last_reference_error A hA g N hN,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_pos ha]
  exact ⟨he ▸ mul_pos ha hnorm,he⟩

/-- The last evaluated physical error has the exact old-flag Pythagorean split.
Use: the arbitrary-method lower bound retains all possible old-flag errors.
Article: main_krylov, thm:exact.
Proof: genuine exhaustion identifies the last reference error; actual conjugacy
becomes Euclidean orthogonality under the true positive metric root. -/
theorem last_evaluation_pythagoras (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin m)) (N : ℕ) (hN : referenceAtomCount A hA g=N+1)
    (v : EuclideanSpace ℝ (Fin m)) (hv : v∈CG.krylovSpace (cgOperator A) g N) (t : ℝ) :
    ‖cgOperator (metricRoot A)⁻¹ (g+cgOperator A
      (CG.displacement (cgOperator A) g N+v+t • CG.direction (cgOperator A) g N))‖^2=
      ‖cgOperator (metricRoot A) v‖^2+(t-CG.length (cgOperator A) g N)^2*
        ‖cgOperator (metricRoot A) (CG.direction (cgOperator A) g N)‖^2 := by
  let Q := cgOperator A
  let R := cgOperator (metricRoot A)
  let J := cgOperator (metricRoot A)⁻¹
  let d := CG.direction Q g N
  let a := CG.length Q g N
  have hbase (w : EuclideanSpace ℝ (Fin m)) : J (Q w)=R w := canonical_reference_action A hA w
  have he : J (g+Q (CG.displacement Q g N+v+t • d))=R v+(t-a) • R d := by
    have hsplit : g+Q (CG.displacement Q g N+v+t • d)=
        (g+Q (CG.displacement Q g N))+Q v+t • Q d := by
      simp only [map_add,map_smul]
      abel
    rw [hsplit,← CG.gradient_displacement]
    simp only [map_add,map_smul]
    change cgCanonicalError A g N+J (Q v)+t • J (Q d)=_
    rw [last_reference_error A hA g N hN,hbase,hbase,sub_smul]
    dsimp only [d,a,R,Q]
    rw [neg_smul]
    abel
  have ho : inner ℝ (R v) (R d)=0 := by
    have hh := canonical_search_pairing A hA v (Q d)
    change inner ℝ v (Q d)=inner ℝ (R v) (J (Q d)) at hh
    rw [hbase] at hh
    rw [← hh]
    exact old_flag_conjugate A hA g N (by omega) v hv
  change ‖J (g+Q (CG.displacement Q g N+v+t • d))‖^2=‖R v‖^2+(t-a)^2*‖R d‖^2
  rw [he,norm_add_sq_real,real_inner_smul_right,ho,mul_zero,mul_zero,add_zero,norm_smul,
    Real.norm_eq_abs,mul_pow,sq_abs]

/-- Every last evaluated physical point has at least its relative trial error
in the genuine last CG error normalization.
Use: transfer arbitrary span-restricted methods to the actual two-endpoint
scalar minimax problem without assuming CG consistency.
Article: main_krylov, thm:exact.
Proof: drop the nonnegative old-flag energy from the exact physical Pythagorean
identity and cancel only the proved positive actual last CG line length. -/
theorem last_evaluation_lower (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin m)) (N : ℕ) (hN : referenceAtomCount A hA g=N+1)
    (v : EuclideanSpace ℝ (Fin m)) (hv : v∈CG.krylovSpace (cgOperator A) g N) (t : ℝ) :
    |1-t/CG.length (cgOperator A) g N| *‖cgCanonicalError A g N‖≤
      ‖cgOperator (metricRoot A)⁻¹ (g+cgOperator A
        (CG.displacement (cgOperator A) g N+v+t • CG.direction (cgOperator A) g N))‖ := by
  let a := CG.length (cgOperator A) g N
  let d := CG.direction (cgOperator A) g N
  let R := cgOperator (metricRoot A)
  have hp := cgOperator_positive A hA
  have hlt : N<referenceAtomCount A hA g := by omega
  have hi := CG.invariant _ hp.1 hp.2 g N (fun j hj => cg_nonstagnation A hA g j (hj.trans hlt))
  have ha : 0<a := (CG.invariant_line_pos _ hp.2 g N hi (cg_nonstagnation A hA g N hlt)).2.1
  have hs : |1-t/a| *a=|t-a| := by
    have he : 1-t/a=(a-t)/a := by field_simp
    rw [he,abs_div,abs_of_pos ha,div_mul_cancel₀ _ ha.ne',abs_sub_comm]
  have he := last_evaluation_pythagoras A hA g N hN v hv t
  rw [(last_reference_denominator A hA g N hN).2,← mul_assoc]
  change |1-t/a| *a*‖R d‖≤_
  rw [hs]
  have hn : 0≤|t-a| *‖R d‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  nlinarith [sq_nonneg ‖R v‖,norm_nonneg (cgOperator (metricRoot A)⁻¹
    (g+cgOperator A (CG.displacement (cgOperator A) g N+v+t • d))),sq_abs (t-a)]

end
end krylov.OneGradient
