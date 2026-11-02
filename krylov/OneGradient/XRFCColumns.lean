import krylov.Envelope.XRFCReferenceBidiagonal
import krylov.Envelope.CanonicalTrialSums
import krylov.Stability.ObliqueResponse
set_option autoImplicit false
/-!
Article: main_krylov, apE:Pi, actual full-cycle XRFC oblique coordinates.
Use: construct the source's real chronological step matrix and prove its
inverse domain from the actual nonzero-trial executor.
Source: genuine executed stored-basis independence, actual positive metric root
and the existing exact transported-prefix matrix identity.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Envelope
open scoped BigOperators
variable {n : ℕ}

/-- The actual chronological physical columns recorded by the full-memory XRFC executor.
Use: the source's oblique projectors use actual evaluated steps, not CG steps.
Article: main_krylov, apE:Pi. -/
def xrfcPhysicalColumns (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun a j => (oneGradientStep (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g j.val) a

/-- The actual canonical evaluated-step matrix of the source's full XRFC cycle.
Use: form genuine oblique old-flag projectors from the real recorded trajectory.
Article: main_krylov, apE:Pi, Sigma_0=A^(1/2)[sbar_0,...,sbar_(n-1)]. -/
def xrfcCanonicalColumns (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ := metricRoot base*xrfcPhysicalColumns trial base g

/-- Every actual source canonical column is the true metric-root image of
its original chronological evaluated step.
Use: connect finite matrix projectors directly to the implemented XRFC trajectory.
Article: main_krylov, apE:Pi.
Proof: the actual matrix product is exactly the original metric-root matrix-vector action. -/
theorem xrfc_canonical_column (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    WithLp.toLp 2 (fun a => xrfcCanonicalColumns trial base g a j)=
      cgOperator (metricRoot base) (oneGradientStep (xrfcMethod fullMemory trial)
        (fun _ => cgOperator base) g j.val) := by
  rfl

/-- The actual full-cycle physical and canonical evaluated-step matrices are
both genuinely nonsingular for every original nonzero reference trial sequence.
Use: all inverse oblique flags have their true domains derived from actual CG data.
Article: main_krylov, apE:Pi.
Proof: the genuine positive executed latest model gives independent reversed
stored steps. Reverse them back to their actual chronology, preserve independence
under the real Euclidean coordinate equivalence, then use the actual positive root. -/
theorem xrfc_columns_nonsingular (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount base hb g=n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0) :
    IsUnit (xrfcPhysicalColumns trial base g).det ∧ IsUnit (xrfcCanonicalColumns trial base g).det := by
  let Q := cgOperator base
  let m := xrfcMethod fullMemory trial
  let s := oneGradientStep m (fun _ => Q) g
  let S := fun i : Fin n => s (n-1-i.val)
  have hp := cgOperator_positive base hb
  have hpre (i : ℕ) (hi : i<n) : CG.gradient Q g i≠0 :=
    cg_nonstagnation base hb g i (by rw [hc];exact hi)
  have hdom := (xrfc_full_array_domains trial Q hp.1 hp.2 g n hpre ht n le_rfl).2
  have hunit : IsUnit (correctionCompression S Q).det := by
    rw [← pairModel_quadratic S Q hp.1]
    exact isUnit_iff_ne_zero.mpr hdom
  have hLI := compression_unit_independent S Q hunit
  have hChron : LinearIndependent ℝ (fun i : Fin n => s i.val) := by
    have h := hLI.comp (Fin.revPerm (n := n)) (Fin.revPerm (n := n)).injective
    convert h using 1
    funext i
    change s i.val=s (n-1-i.rev.val)
    congr 1
    rw [Fin.val_rev]
    omega
  have hraw : LinearIndependent ℝ (xrfcPhysicalColumns trial base g).col :=
    hChron.map' (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap
      (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).ker
  have hS : IsUnit (xrfcPhysicalColumns trial base g).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_cols_iff_isUnit.mp hraw)
  refine ⟨hS,?_⟩
  rw [xrfcCanonicalColumns,Matrix.det_mul]
  exact (metricRoot_det_unit base hb).mul hS

/-- A genuine transported old flag selects each original real basis column.
Use: keep the true evaluated-step prefix when applying the actual XRFC projector.
Article: main_krylov, apE:Pi.
Proof: the actual inverse cancels on the column matrix, and its real diagonal
prefix selector retains precisely the known chronological columns. -/
theorem transported_flag_column (T : Matrix (Fin n) (Fin n) ℝ) (hT : IsUnit T.det)
    (l : ℕ) (j : Fin n) :
    cgOperator (transportedFlag T l) (WithLp.toLp 2 (fun a => T a j))=
      if j.val≤l then WithLp.toLp 2 (fun a => T a j) else 0 := by
  change WithLp.toLp 2 (fun a => (transportedFlag T l*T) a j)=_
  rw [transportedFlag_column_mul T hT]
  ext a
  simp only [Matrix.mul_diagonal,prefixProjection]
  split_ifs <;> simp

end
end krylov.OneGradient
