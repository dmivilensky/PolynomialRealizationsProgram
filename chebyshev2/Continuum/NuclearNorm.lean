import chebyshev2.Continuum.TraceBound

/-!
Article: chebyshev2, Theorem 2.3.
The nuclear norm in its finite-frame dual definition.
Use: `chebyshev2.Continuum.densityOperator_isTraceClass` feeds
`chebyshev2.Continuum.kernelEigenvalue_square_integral` (The quadratic spectral observation is
the literal double integral printed in Section 2.2, for every nonnegative integrable density).
Proof chain: `chebyshev2.Packing.packed_spectral_distance` — chebyshev2, Theorem 2.3; Block
packing, exact masses/energy and spectral distance.
Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus. The
needed form is proved here.
-/
namespace chebyshev2.Continuum
noncomputable section
open scoped InnerProductSpace BigOperators ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/--
The nuclear norm in its finite-frame dual definition. Using ENNReal records infinite norm
instead of silently assigning zero to a divergent supremum.

Use: `chebyshev2.Continuum.IsTraceClass` uses this definition in the displayed construction
of `IsTraceClass`. Its inputs and component formulas are fixed by that definition.

Article: chebyshev2, Theorem 2.4 via `chebyshev2.Continuum.eigenvalue_l1_le_nuclearNorm`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.
-/
def nuclearNorm (T : E →L[ℝ] E) : ℝ≥0∞ :=
  ⨆ n : ℕ, ⨆ u : Fin n → E, ⨆ v : Fin n → E,
    ⨆ (_ : Orthonormal ℝ u), ⨆ (_ : Orthonormal ℝ v),
      ENNReal.ofReal |∑ i, inner ℝ (u i) (T (v i))|

/--
Defines `IsTraceClass` of type `Prop` by `nuclearNorm T < ⊤`.

Use: `chebyshev2.Continuum.TraceBound.isTraceClass` uses this definition to establish the
trace-class property: `IsTraceClass T`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.
-/
def IsTraceClass (T : E →L[ℝ] E) : Prop := nuclearNorm T < ⊤

/--
The stated quantitative bound `nuclearNorm T ≤ ENNReal.ofReal C`.

Use: `chebyshev2.Continuum.TraceBound.isTraceClass` uses this bound to establish the
trace-class property: `IsTraceClass T`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem nuclearNorm_le_of_traceBound {T : E →L[ℝ] E} {C : ℝ} (h : TraceBound T C) :
    nuclearNorm T ≤ ENNReal.ofReal C := by
  simp only [nuclearNorm, iSup_le_iff]
  intro n u v hu hv
  exact ENNReal.ofReal_le_ofReal (h n u v hu hv)

/--
The precise assertion is `TraceBound T C`.

Use: `chebyshev2.Continuum.IsTraceClass.traceBound` uses this assertion to establish the
precise assertion is `TraceBound T (nuclearNorm T).toReal`.

Article: chebyshev2, Theorem 2.4 via `chebyshev2.Continuum.eigenvalue_l1_le_nuclearNorm`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem traceBound_of_nuclearNorm_le {T : E →L[ℝ] E} {C : ℝ} (hC : 0 ≤ C)
    (h : nuclearNorm T ≤ ENNReal.ofReal C) : TraceBound T C := by
  intro n u v hu hv
  have hl : ENNReal.ofReal |∑ i, inner ℝ (u i) (T (v i))| ≤ nuclearNorm T := by
    exact le_iSup_of_le n (le_iSup_of_le u (le_iSup_of_le v
      (le_iSup_of_le hu (le_iSup_of_le hv le_rfl))))
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp (hl.trans h)

/--
The trace-class property: `IsTraceClass T`.

Use: `chebyshev2.Continuum.densityOperator_isTraceClass` uses this assertion to establish
the trace-class property: `IsTraceClass (densityOperator m)`.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Use the identities/estimates `chebyshev2.Continuum.nuclearNorm_le_of_traceBound`
with the arguments shown in the proof.
-/
theorem TraceBound.isTraceClass {T : E →L[ℝ] E} {C : ℝ} (h : TraceBound T C) : IsTraceClass T :=
  (nuclearNorm_le_of_traceBound h).trans_lt ENNReal.ofReal_lt_top

/--
The trace-class property: `IsTraceClass (InnerProductSpace.rankOne ℝ a b)`.

Use: `chebyshev2.Continuum.rankOne_logDeterminant` uses this assertion to establish exact
identity `logDeterminant D'.eigenvalue s = logDeterminant D.eigenvalue s+ log (1+s/2*u*inner ℝ
v (inverseOfUnit _ (positive_pencil_unit hp (show 0 ≤ s/2 by positivity)) v))`.

Article: chebyshev2, Theorem 3.3 via `chebyshev2.HalfLine.commonMeasure_ode_probability`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Use the identities/estimates `chebyshev2.Continuum.TraceBound.isTraceClass`,
`chebyshev2.Continuum.traceBound_rankOne` with the arguments shown in the proof.
-/
theorem rankOne_isTraceClass (a b : E) : IsTraceClass (InnerProductSpace.rankOne ℝ a b) :=
  (traceBound_rankOne a b).isTraceClass

/--
The trace-class property: `IsTraceClass (densityOperator m)`.

Use: `chebyshev2.Continuum.densitySpectralData` uses this assertion in the displayed
construction of `densitySpectralData`. Its inputs and component formulas are fixed by that
definition.

Article: chebyshev2, Theorem 2.3 via `chebyshev2.Packing.packed_spectral_distance`.

Source: Simon, Trace Ideals and Their Applications — nuclear/trace-class operator calculus.

Proof: Use the identities/estimates `chebyshev2.Continuum.TraceBound.isTraceClass`,
`chebyshev2.Continuum.densityOperator_traceBound` with the arguments shown in the proof.
-/
theorem densityOperator_isTraceClass {m : ℝ → ℝ} (hm : MeasureTheory.Integrable m) :
    IsTraceClass (densityOperator m) := (densityOperator_traceBound hm).isTraceClass

end
end chebyshev2.Continuum
