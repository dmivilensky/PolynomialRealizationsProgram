import krylov.Methods.SmoothProbedFields

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(d), genuine zero-mismatch pairing derivative.
Use: differentiate actual step/operator-defect/step pairings at a true
zero operator defect without retaining spurious step-variation terms.
Source: standard real inner-product and actual continuous-linear operator
application derivative rules from mathlib.
-/

namespace krylov.Envelope
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- At a genuine zero operator mismatch, the true step/mismatch/step pairing derivative depends only on the actual operator derivative and real reference vectors.
Use: At a genuine zero operator mismatch, the true step/mismatch/step pairing derivative depends only on the actual operator derivative and real reference vectors.
Article: main_krylov, apB:lem:mu(d), genuine zero-mismatch pairing derivative.
Proof: Apply the genuine operator and inner-product product rules; both true vector-derivative contributions contain the actual zero reference operator. -/
theorem zero_operator_pair_hasDeriv (s v : ℝ → E) (T : ℝ → E →L[ℝ] E)
    (ds dv : E) (D : E →L[ℝ] E)
    (hs : HasDerivAt s ds 0) (hv : HasDerivAt v dv 0) (hT : HasDerivAt T D 0) (hzero : T 0=0) :
    HasDerivAt (fun t => inner ℝ (s t) (T t (v t))) (inner ℝ (s 0) (D (v 0))) 0 := by
  have hh := hs.inner ℝ (hT.clm_apply hv)
  simpa only [hzero,_root_.zero_apply,zero_add,inner_zero_right,add_zero] using hh
end
end krylov.Envelope
