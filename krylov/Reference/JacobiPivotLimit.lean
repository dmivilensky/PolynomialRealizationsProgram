import krylov.Reference.JacobiPivots
import krylov.Reference.HeavyBallParameters
import krylov.LinearAlgebra.PositivePivotLimit
set_option autoImplicit false
/-!
Article: main_krylov, prop:phi(c), true measured Nevai pivot limit.
Use: derive convergence of actual original principal determinant ratios from original coefficient limits and genuine physical spectral forms.
Source: actual finite Jacobi LDL recurrences, strict shifted principal domains and the proved positive Riccati stability theorem.
-/

namespace krylov.Reference
noncomputable section
open Matrix Filter chebyshev1 krylov.LinearAlgebra
open scoped Topology

/-- Each actual positive Jacobi determinant pivot is bounded above by its original physical diagonal entry.
Use: Each actual positive Jacobi determinant pivot is bounded above by its original physical diagonal entry.
Article: main_krylov, prop:phi(c), true measured Nevai pivot limit.
Proof: The true Riccati recurrence subtracts a nonnegative squared edge over a positive principal pivot. -/
theorem jacobiPivot_le_diagonal (A B : ℕ → ℝ) (hB : ∀ n,0<B n)
    (hpos : ∀ N,(jacobiPrefix A B N).PosDef) (n : ℕ) : jacobiPivot A B n≤A n := by
  cases n with
  | zero => rw [jacobiPivot_zero]
  | succ n =>
    rw [jacobiPivot_recurrence A B hB hpos]
    exact sub_le_self _ (div_nonneg (sq_nonneg _) (jacobiPivot_pos A B hpos n).le)

/-- Every actual principal pivot obeys the genuine original physical upper spectral bound.
Use: Every actual principal pivot obeys the genuine original physical upper spectral bound.
Article: main_krylov, prop:phi(c), true measured Nevai pivot limit.
Proof: Combine the original diagonal shifted-form test with the true pivot recurrence bound. -/
theorem jacobiPivot_physical_cap (A B : ℕ → ℝ) (hB : ∀ n,0<B n)
    (hpos : ∀ N,(jacobiPrefix A B N).PosDef) (L : ℝ)
    (hup : ∀ N,(L • (1 : Matrix (Fin N) (Fin N) ℝ)-jacobiPrefix A B N).PosSemidef) (n : ℕ) :
    jacobiPivot A B n≤L := by
  have h := (hup (n+1)).diag_nonneg (i := Fin.last n)
  simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one,
    jacobiPrefix_diagonal,Fin.val_last] at h
  exact (jacobiPivot_le_diagonal A B hB hpos n).trans (by linarith)

/-- The actual original Jacobi determinant pivots converge to the printed stable heavy-ball pivot under the genuine Nevai coefficient limits.
Use: The actual original Jacobi determinant pivots converge to the printed stable heavy-ball pivot under the genuine Nevai coefficient limits.
Article: main_krylov, prop:phi(c), true measured Nevai pivot limit.
Proof: Derive positive original and shifted pivots, their exact recurrences, initial shift gap and physical cap, then apply proved scalar Riccati stability. -/
theorem jacobiPivot_nevai_limit (A B : ℕ → ℝ) (I : SpectralInterval) (hB : ∀ n,0<B n)
    (hlo : ∀ N,(jacobiPrefix A B N-I.mu • 1).PosSemidef)
    (hup : ∀ N,(I.L • (1 : Matrix (Fin N) (Fin N) ℝ)-jacobiPrefix A B N).PosSemidef)
    (hA : Tendsto A atTop (𝓝 ((I.L+I.mu)/2)))
    (hBl : Tendsto B atTop (𝓝 ((I.L-I.mu)/4))) :
    Tendsto (jacobiPivot A B) atTop (𝓝 (HeavyBallParameters.pivot I)) := by
  -- Derive both genuine determinant-pivot domains before invoking scalar stability for the actual original recurrences.
  let d := jacobiPivot A B
  let s := jacobiPivot (fun n => A n-I.mu) B
  have hpos (N : ℕ) : (jacobiPrefix A B N).PosDef := jacobiPrefix_posDef A B I.mu I.mu_pos N (hlo N)
  have hspos := jacobiPrefix_shift_posDef A B I.mu hB hlo
  have hd := HeavyBallParameters.pivot_pos I
  have hq := HeavyBallParameters.ratio_domain I
  have he := HeavyBallParameters.edge I
  have ha := HeavyBallParameters.diagonal I
  have hm := HeavyBallParameters.lower_endpoint I
  have hb : 0<(I.L-I.mu)/4 := by linarith [I.mu_lt_L]
  have hD : (I.L-I.mu)/4<HeavyBallParameters.pivot I := by
    rw [← he]
    exact mul_lt_of_lt_one_right hd hq.2
  -- The printed square-root pivot is the stable fixed point of the actual limiting Jacobi recurrence.
  have hfix : (I.L+I.mu)/2=HeavyBallParameters.pivot I+
      ((I.L-I.mu)/4)^2/HeavyBallParameters.pivot I := by
    rw [← ha,← he]
    field_simp
  apply positive_pivot_limit d s A B I.mu I.L ((I.L+I.mu)/2) ((I.L-I.mu)/4)
    (HeavyBallParameters.pivot I) I.mu_pos hb hD hfix (by ring)
    (jacobiPivot_pos A B hpos) (jacobiPivot_pos _ B hspos) _
    (jacobiPivot_physical_cap A B hB hpos I.L hup)
    (jacobiPivot_recurrence A B hB hpos) (jacobiPivot_recurrence _ B hB hspos) hA hBl
  rw [show d 0=A 0 from jacobiPivot_zero A B,show s 0=A 0-I.mu from jacobiPivot_zero _ B]
  ring
end
end krylov.Reference
