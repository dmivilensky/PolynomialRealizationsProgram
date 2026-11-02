import jacobi.Variational.FredholmGreen
import jacobi.Variational.Congruence

/-!
Article: jacobi, Theorem D.7.
Almost-everywhere changes preserve the actual feature operator, its actual
two-sided resolvent and the complete Green kernel. This allows the measurable
minimizer to be replaced by the continuous Euler representative without
silently changing its integral operator or its Green differential equation.
Source: Bochner integral congruence and uniqueness of an actual two-sided inverse.
Use: transfers the original minimizing operator to its continuous Euler representative.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational chebyshev2.Continuum
set_option backward.isDefEq.respectTransparency false

/-- Null-set changes preserve the literal feature operator on the common Hilbert space.
Use: transfers the original minimizing operator to its continuous Euler representative.
Article: jacobi, Theorem D.7.
Proof: the actual operator-valued Bochner integrands agree almost everywhere. -/
theorem operator_congr {m q : L1Source} (he : m.value=ᵐ[volume] q.value) :
    densityOperator m.value=densityOperator q.value := by
  unfold densityOperator
  exact integral_congr_ae (he.mono fun x hx => congrArg (fun r : ℝ => r • featureProjection x) hx)

/-- Null-set changes preserve the genuine inverse pencil, for any separately proved subcritical margins.
Use: the continuous representative retains the complete original Green kernel.
Article: jacobi, Theorem D.7.
Proof: the actual pencils are equal. Their already proved two-sided inverse identities force equality of the actual inverses. -/
theorem resolvent_congr {m q : L1Source} (he : m.value=ᵐ[volume] q.value) {s : ℝ}
    (hs : 0≤s) (hm : s*observe m .top<1) (hq : s*observe q .top<1) :
    m.fredholmResolvent s hs hm=q.fredholmResolvent s hs hq := by
  -- Cancel only the proved genuine inverse pencil, rather than rewriting its choice implementation.
  have hp : m.fredholmPencil s=q.fredholmPencil s := by
    unfold L1Source.fredholmPencil
    rw [operator_congr he]
  apply ContinuousLinearMap.ext
  intro u
  calc
    m.fredholmResolvent s hs hm u=
        m.fredholmResolvent s hs hm (q.fredholmPencil s (q.fredholmResolvent s hs hq u)) := by rw [q.pencil_resolvent]
    _ =m.fredholmResolvent s hs hm (m.fredholmPencil s (q.fredholmResolvent s hs hq u)) := by rw [hp]
    _ =q.fredholmResolvent s hs hq u := m.resolvent_pencil hs hm _

/-- The entire actual Green kernel is unchanged by replacing the density on a null set.
Use: upgrades the original Fredholm optimizer to classical regularity with its original determinant and diagonal retained.
Article: jacobi, Theorem D.7.
Proof: substitute the proved equal actual resolvents in the literal feature pairing. -/
theorem green_congr {m q : L1Source} (he : m.value=ᵐ[volume] q.value) {s : ℝ}
    (hs : 0≤s) (hm : s*observe m .top<1) (hq : s*observe q .top<1) :
    m.fredholmGreen s hs hm=q.fredholmGreen s hs hq := by
  unfold L1Source.fredholmGreen
  rw [resolvent_congr he hs hm hq]

end
end jacobi.Fredholm
