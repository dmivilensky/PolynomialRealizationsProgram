import krylov.Convergence.VirtualTrialGeometry
import krylov.Convergence.VirtualDirectionTensorBound
import krylov.Convergence.VirtualDirectionMidpoints

/-!
Article: main_krylov, thm:V, near-exact trials shrink the true coefficient.
Use: retain a uniform estimate along arbitrary varying reference directions,
including exact trials. Source: the genuine chronological amplitude product,
compact derived geometry and both printed compatible tensor norm bounds.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set krylov.Methods krylov.Reference krylov.Functions krylov.Stability
  krylov.OneGradient krylov.Secant krylov.Envelope
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- On the true compact family the two original tensor coefficients
are bounded by an absolute family constant times the largest genuine
reference trial miss. Neither an amplitude nor a projector bound is an
extra source premise. Article: main_krylov, thm:V. -/
theorem xrfc_compact_near_exact_tensor_coefficients
    (trial : History E → ℝ) (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (U : Set E) (hU : IsCompact U)
    (hcount : ∀ u∈U,referenceAtomCount base hb (cgOperator base u)=n)
    (ht : ∀ u∈U,∀ i<n,0<trial (oneGradientRun (xrfcMethod fullMemory trial)
      (fun _=>cgOperator base) (cgOperator base u) i))
    (hT : ∀ u∈U,∀ i<n,ContDiffAt ℝ 2 (trialCoordinate trial i)
      (oneGradientData (xrfcMethod fullMemory trial) (fun _=>cgOperator base) (cgOperator base u) i))
    (D : E →L[ℝ] E →L[ℝ] E) (M : ℝ) (hM : 0≤M)
    (hbudget : ∀ v,‖cgOperator (metricRoot base)⁻¹*(D v)*cgOperator (metricRoot base)⁻¹‖≤
      M*‖cgOperator (metricRoot base) v‖) :
    ∃ C : ℝ,0<C ∧∀ u∈U,∀ delta : ℝ,0≤delta →
      (∀ l<n,|xrfcTrialError trial base (cgOperator base u) l|≤delta) →
      ‖xrfcTensorCoefficient trial base D u‖≤C*delta ∧
      ‖xrfcDTensorCoefficient trial base D u‖≤C*delta := by
  obtain ⟨B,hB,hgeometry⟩ := xrfc_compact_trial_geometry trial base hb U hU hcount ht hT
  refine ⟨M*B+1,by positivity,?_⟩
  intro u hu delta hd herr
  let g := cgOperator base u
  let P := fun l=>‖cgOperator (transportedFlag (xrfcCanonicalColumns trial base g) l)‖
  let W := fun l=>‖cgOperator (metricRoot base) (xrfcReferenceMidpointDrift trial (cgOperator base) u l)‖
  have hsumbound (p : ℕ → ℝ) (hp0 : ∀ l,0≤p l) (hp : ∀ l,p l≤1+P l) :
      ∑ l∈Finset.range n,|xrfcTrialCoefficient trial base g n l| * p l*W l≤delta*B := by
    calc
      _ ≤ ∑ l∈Finset.range n,delta*(xrfcTrialTailMagnitude trial base u l*(1+P l)*W l) := by
        apply Finset.sum_le_sum
        intro l hl
        have hln := Finset.mem_range.mp hl
        rw [xrfcTrialCoefficient_abs_tail trial base hb u (hcount u hu) l hln]
        have htail : 0≤xrfcTrialTailMagnitude trial base u l := by
          dsimp only [xrfcTrialTailMagnitude]
          positivity
        have hh := mul_le_mul (herr l hln) (hp l) (hp0 l) hd
        have hh' := mul_le_mul_of_nonneg_right hh
          (mul_nonneg htail (norm_nonneg (cgOperator (metricRoot base)
            (xrfcReferenceMidpointDrift trial (cgOperator base) u l))))
        dsimp only [W]
        nlinarith only [hh']
      _ = delta*∑ l∈Finset.range n,xrfcTrialTailMagnitude trial base u l*(1+P l)*W l := by
        rw [Finset.mul_sum]
      _ ≤ delta*B := mul_le_mul_of_nonneg_left (hgeometry u hu) hd
  have hbound : M*(delta*B)≤(M*B+1)*delta := by nlinarith only [hd]
  constructor
  · exact (xrfcTensorCoefficient_norm_bound trial base hb D u (hcount u hu) M hbudget).trans
      ((mul_le_mul_of_nonneg_left (hsumbound P (fun _=>norm_nonneg _) (fun _=>by linarith)) hM).trans hbound)
  · have htrialD (i : ℕ) (hi : i<n) : trial (oneGradientRun (xrfcDMethod fullMemory trial)
        (fun _=>cgOperator base) g i)≠0 := by
      rw [xrfc_quadratic_basis_histories trial (cgOperator base) (cgOperator_positive base hb).1
        (cgOperator_positive base hb).2 g n
        (fun j hj=>cg_nonstagnation base hb g j (by rw [hcount u hu];exact hj))
        (fun j hj=>(ht u hu j hj).ne') i hi.le]
      exact (ht u hu i hi).ne'
    have hh := xrfcDTensorCoefficient_norm_bound trial base hb D u (hcount u hu) M hbudget
    simp_rw [xrfcDReferenceMidpointDrift_eq_step trial base hb u (hcount u hu) htrialD] at hh
    have hs := hsumbound (fun _=>1) (fun _=>zero_le_one) (fun l=>by dsimp only [P];linarith only [norm_nonneg (cgOperator (transportedFlag (xrfcCanonicalColumns trial base g) l))])
    simp only [mul_one] at hs
    exact hh.trans ((mul_le_mul_of_nonneg_left hs hM).trans hbound)

end
end krylov.Convergence
