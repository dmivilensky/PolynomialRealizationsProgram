import krylov.Stability.ContDiffXRFC
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, actual XRFC virtual physical trajectory.
Use: distinguish the actual evaluated and unevaluated physical displacements and express the genuine virtual step by true executed queries and corrections.
Source: the original one-gradient executor, actual output displacement and genuine telescoping finite histories.
-/

namespace krylov.Methods
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual physical virtual point of the genuine full-memory XRFC execution.
Use: The actual physical virtual point of the genuine full-memory XRFC execution.
Article: main_krylov, thm:E1, actual XRFC virtual physical trajectory.
Proof: Add the real computed final virtual correction to the actual evaluated history displacement. -/
def xrfcVirtualPoint (trial : History E → ℝ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  (xrfcMethod fullMemory trial).outputDisplacement (oneGradientRun (xrfcMethod fullMemory trial) A g k)

/-- The genuine extrapolated virtual gradient formed from the actual full-memory XRFC observed history.
Use: The genuine extrapolated virtual gradient formed from the actual full-memory XRFC observed history.
Article: main_krylov, thm:E1, actual XRFC virtual physical trajectory.
Proof: Apply the true latest-model extrapolation to the actual stored secants and returned gradient. -/
def xrfcVirtualGradient (trial : History E → ℝ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  virtualGradient (selectedWindow fullMemory (oneGradientRun (xrfcMethod fullMemory trial) A g k))
    (oneGradientGradient (xrfcMethod fullMemory trial) A g k)

/-- The actual difference of consecutive genuine full-memory XRFC virtual physical points.
Use: The actual difference of consecutive genuine full-memory XRFC virtual physical points.
Article: main_krylov, thm:E1, actual XRFC virtual physical trajectory.
Proof: Subtract the two real unevaluated output displacements. -/
def xrfcVirtualStep (trial : History E → ℝ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  xrfcVirtualPoint trial A g (k+1)-xrfcVirtualPoint trial A g k

/-- The genuine XRFC virtual step is its actual evaluated query plus the true change of computed virtual corrections.
Use: The genuine XRFC virtual step is its actual evaluated query plus the true change of computed virtual corrections.
Article: main_krylov, thm:E1, actual XRFC virtual physical trajectory.
Proof: Telescope the original physical one-gradient history displacements. -/
theorem xrfcVirtualStep_corrections (trial : History E → ℝ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    let m := xrfcMethod fullMemory trial (E := E)
    let H := fun i => oneGradientRun m A g i
    xrfcVirtualStep trial A g k=oneGradientStep m A g k+m.output (H (k+1))-m.output (H k) := by
  dsimp only [xrfcVirtualStep,xrfcVirtualPoint,OneGradientMethod.outputDisplacement]
  rw [oneGradientRun_displacement_sum,oneGradientRun_displacement_sum,Finset.sum_range_succ]
  abel

/-- The actual XRFC virtual point equals the genuine chronological sum of its true virtual steps.
Use: The actual XRFC virtual point equals the genuine chronological sum of its true virtual steps.
Article: main_krylov, thm:E1, actual XRFC virtual physical trajectory.
Proof: The real initial virtual correction is empty; the actual consecutive differences telescope. -/
theorem xrfcVirtualPoint_sum (trial : History E → ℝ) (A : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    xrfcVirtualPoint trial A g k=∑ i∈Finset.range k,xrfcVirtualStep trial A g i := by
  -- Start from the actual empty output solve and telescope the genuine consecutive virtual points.
  induction k with
  | zero =>
    simp [xrfcVirtualPoint,xrfcMethod,oneGradientRun,OneGradientMethod.outputDisplacement,
      virtualCorrection,combine,selectedWindow,fullMemory,History.pairs,History.displacement]
    exact Finset.sum_eq_zero (fun i _ => Fin.elim0 i)
  | succ k ih =>
    rw [Finset.sum_range_succ,← ih,xrfcVirtualStep]
    abel
end
end krylov.Methods
