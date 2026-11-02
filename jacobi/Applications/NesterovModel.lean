import chebyshev1.Realization.Expansion
import chebyshev1.Realization.Gain

/-!
Article: jacobi, Theorem 5.1.
The original Nesterov iteration is a genuine two-memory realization in
the first article's operator-transfer and first-variation framework.
Use: its actual kernel, rather than a separately postulated formula,
is computed in NesterovKernel and maximized in NesterovGain.
-/
namespace jacobi.Applications
noncomputable section
open Matrix chebyshev1
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The original momentum coefficient, with its separately specified initial Landweber step.
Use: nesterovMethod implements exactly the original recurrence for every b>-1.
Article: jacobi, Theorem 5.1.
-/
def nesterovMomentum (b:ℝ) (s:ℕ) : ℝ := if s=0 then 0 else ((s:ℝ)-1)/((s:ℝ)+b)

/-- The actual two-memory realization of the original Nesterov method, storing current and previous errors.
Use: NesterovKernel computes its genuine first-variation kernel using the reused causal operator-transfer calculus.
Article: jacobi, Theorem 5.1.
-/
def nesterovMethod (b:ℝ) : Realization (Fin 2) where
  b := ![1,1]
  readout := ![1,0]
  P s := !![1+nesterovMomentum b s,-nesterovMomentum b s;1,0]
  g _ := ![1,0]
  q s := ![1+nesterovMomentum b s,-nesterovMomentum b s]

/-- The actual spectral step is exactly the Nesterov query followed by its Landweber action and the unchanged memory shift.
Use: derives both unperturbed queries and insertion propagation for the actual realization.
Article: jacobi, Theorem 5.1.
Proof: evaluate the original rank-one query factor in the generic realization definition. -/
theorem nesterov_scalarStep (b:ℝ) (s:ℕ) (l:ℝ) :
    (nesterovMethod b).scalarStep s l=
      !![(1-l)*(1+nesterovMomentum b s),-(1-l)*nesterovMomentum b s;1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Realization.scalarStep,Realization.queryFactor,nesterovMethod,Matrix.vecMulVec] <;> ring

/-- The actual initial query is the initial error, and its memory transition is one Landweber step.
Use: initializes all fixed-operator and first-variation formulas, including the k=1 horizon.
Article: jacobi, Theorem 5.1.
Proof: the separately specified initial momentum is zero. -/
@[simp] theorem nesterovMomentum_zero (b:ℝ) : nesterovMomentum b 0=0 := by simp [nesterovMomentum]

/-- At b=1 every positive-step momentum is the exact rational rescaling used in the constant-coefficient wave equation.
Use: the transformation v_s=s*e_s proves the actual Nesterov insertion propagator.
Article: jacobi, Theorem 5.1.
Proof: positive steps select the original rational branch. -/
theorem nesterovMomentum_one {s:ℕ} (hs:0<s) :
    nesterovMomentum 1 s=((s:ℝ)-1)/((s:ℝ)+1) := by
  simp only [nesterovMomentum,ite_eq_right (Nat.ne_of_gt hs)]

/-- For every admissible original momentum parameter the positive-step denominator is genuinely positive.
Use: no propagation or endpoint-gain formula relies on a totalized zero denominator.
Article: jacobi, Theorem 5.1.
Proof: a positive natural step is at least one and b is strictly greater than minus one. -/
theorem nesterov_denominator_pos {b:ℝ} (hb:-1<b) {s:ℕ} (hs:0<s) : 0<(s:ℝ)+b := by
  have hn : (1:ℝ)≤s := by exact_mod_cast hs
  linarith

end
end jacobi.Applications
