import krylov.LinearAlgebra.BidiagonalFlag
import krylov.OneGradient.XRFCProjector
import krylov.Reference.EnergyPositive
set_option autoImplicit false
/-!
Article: main_krylov, apE:Pi, actual canonical bidiagonal XRFC geometry.
Use: identify every original oblique projector column with its printed
CG-coordinate product, including exact trials and zero off-diagonal entries.
Source: actual executed XRFC reference steps, positive CG energies/lengths
and the proved finite nonzero-diagonal back substitution.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Stability krylov.Envelope krylov.LinearAlgebra
open scoped BigOperators
variable {n : ℕ}

/-- The original relative error of an actual measured XRFC reference trial.
Use: express the true canonical bidiagonal coefficients in source notation.
Article: main_krylov, apE:Pi, epsilon_j=1-tau_j/alpha_j. -/
def xrfcTrialError (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (j : ℕ) : ℝ :=
  1-trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g j)/
    CG.length (cgOperator base) g j

/-- The genuine nonzero diagonal of the canonical evaluated-step matrix.
Use: only this original nonzero trial factor is inverted in the projector formula.
Article: main_krylov, apE:Pi. -/
def xrfcCanonicalDiagonal (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (j : ℕ) : ℝ :=
  (1-xrfcTrialError trial base g j)*Real.sqrt (cgEnergy base g j)

/-- The genuine preceding missed-line coefficient of a canonical evaluated step.
Use: keep zero coefficients when an actual reference trial is exact.
Article: main_krylov, apE:Pi. -/
def xrfcCanonicalOffDiagonal (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (j : ℕ) : ℝ :=
  xrfcTrialError trial base g j*Real.sqrt (cgEnergy base g j)

/-- The actual initial and subsequent evaluated canonical steps have the
literal original two-term CG-coordinate form.
Use: derive the oblique flag geometry from the actual execution.
Article: main_krylov, apE:Pi, Sigma_0 is upper bidiagonal in the unit CG frame.
Proof: apply the true metric root to the proved initial and subsequent XRFC
query formulas, then use the actual missed-line normalization. -/
theorem xrfc_canonical_step_bidiagonal
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount base hb g=n) (hn : 0<n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0) :
    let m := xrfcMethod fullMemory trial
    let s := fun j => cgOperator (metricRoot base) (oneGradientStep m (fun _ => cgOperator base) g j)
    s 0=xrfcCanonicalDiagonal trial base g 0 • canonicalCGUnitStep base g 0 ∧
      ∀ j,j+1<n → s (j+1)=
        xrfcCanonicalOffDiagonal trial base g j • canonicalCGUnitStep base g j+
        xrfcCanonicalDiagonal trial base g (j+1) • canonicalCGUnitStep base g (j+1) := by
  have hp := cgOperator_positive base hb
  have hpre (i : ℕ) (hi : i<n) : CG.gradient (cgOperator base) g i≠0 :=
    cg_nonstagnation base hb g i (by rw [hc];exact hi)
  have hnorm (j : ℕ) (hj : j<n) (rho : ℝ) :=
    canonical_missed_line base hb g j (by rw [hc];exact hj) rho
  dsimp only
  constructor
  · rw [xrfc_reference_step_zero,hnorm 0 hn]
    congr 1
    simp only [xrfcCanonicalDiagonal,xrfcTrialError,sub_sub_cancel]
  · intro j hj
    change cgOperator (metricRoot base) ((xrfcMethod fullMemory trial).step
      (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g (j+1)))=_
    rw [xrfc_full_step_succ trial (cgOperator base) hp.1 hp.2 g n hpre ht j hj,
      map_add,hnorm j (by omega),hnorm (j+1) hj]
    congr 1
    · congr 1
      dsimp only [xrfcCanonicalOffDiagonal,xrfcTrialError]
      rw [sub_div,div_self (cgLength_pos base hb g j (by rw [hc];omega)).ne']
    · congr 1
      simp only [xrfcCanonicalDiagonal,xrfcTrialError,sub_sub_cancel]

/-- The true canonical diagonal is nonzero under precisely the original
nonzero-trial and active-reference assumptions.
Use: justify every printed r_lk division from actual physical data.
Article: main_krylov, apE:Pi.
Proof: the actual trial and CG length are nonzero, and active CG energy is positive. -/
theorem xrfc_canonical_diagonal_ne_zero
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount base hb g=n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (j : ℕ) (hj : j<n) : xrfcCanonicalDiagonal trial base g j≠0 := by
  have hjc : j<referenceAtomCount base hb g := by rw [hc];exact hj
  simp only [xrfcCanonicalDiagonal,xrfcTrialError,sub_sub_cancel]
  exact mul_ne_zero (div_ne_zero (ht j hj) (cgLength_pos base hb g j hjc).ne')
    (Real.sqrt_pos.mpr (cgEnergy_pos base hb g j hjc)).ne'

/-- The original chronological product giving a real oblique tail column.
Use: record the exact source row without a nonzero-amplitude premise.
Article: main_krylov, apE:Pi, r_lk. -/
def xrfcFlagCoefficient (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (l k : ℕ) : ℝ :=
  ∏ j∈Finset.Ico (l+1) (k+1),
    -xrfcCanonicalOffDiagonal trial base g (j-1)/xrfcCanonicalDiagonal trial base g j

/-- The actual evaluated-step oblique projector preserves every old CG unit
step and maps every later one to the printed product times its boundary unit step.
Use: the full original inverse-column formula, with exact trials retained.
Article: main_krylov, apE:Pi.
Proof: the actual nonsingular executed columns give true prefix selection;
the genuine bidiagonal reference identity and derived nonzero diagonal allow
finite triangular back substitution. -/
theorem xrfc_projector_unit_columns
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (hc : referenceAtomCount base hb g=n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator base) g i)≠0)
    (l : ℕ) (hl : l<n) (k : ℕ) (hk : k<n) :
    let P := cgOperator (transportedFlag (xrfcCanonicalColumns trial base g) l)
    P (canonicalCGUnitStep base g k)=if k≤l then canonicalCGUnitStep base g k
      else xrfcFlagCoefficient trial base g l k • canonicalCGUnitStep base g l := by
  let m := xrfcMethod fullMemory trial
  let T := xrfcCanonicalColumns trial base g
  let s := fun j => cgOperator (metricRoot base) (oneGradientStep m (fun _ => cgOperator base) g j)
  let P := cgOperator (transportedFlag T l)
  have hs := xrfc_canonical_step_bidiagonal trial base hb g hc (by omega) ht
  have hP (j : ℕ) (hj : j<n) : P (s j)=if j≤l then s j else 0 := by
    have h := transported_flag_column T (xrfc_columns_nonsingular trial base hb g hc ht).2 l ⟨j,hj⟩
    change cgOperator (transportedFlag (xrfcCanonicalColumns trial base g) l)
      (WithLp.toLp 2 (fun a => xrfcCanonicalColumns trial base g a ⟨j,hj⟩))=_ at h
    rw [xrfc_canonical_column] at h
    split_ifs at h ⊢ <;> exact h
  have hb' := xrfc_canonical_diagonal_ne_zero trial base hb g hc ht
  dsimp only
  split_ifs with hkl
  · exact bidiagonal_flag_prefix P (canonicalCGUnitStep base g) s _ _ n l hb' hs.1 hs.2 hP k hk hkl
  · exact bidiagonal_flag_tail P (canonicalCGUnitStep base g) s _ _ n l hb' hs.1 hs.2 hP k hk (by omega)

end
end krylov.OneGradient
