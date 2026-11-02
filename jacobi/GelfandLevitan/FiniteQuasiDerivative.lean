import jacobi.GelfandLevitan.FiniteSolutionEquation

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The original finite transformed solution satisfies the genuine
quasi-derivative identity. Its right-hand side contains the diagonal
w^(N), not its derivative. This is the finite identity needed for the
subsequent passage to the actual infinite GL solution.
Use: finiteTransformedQuasiDerivative_hasDerivWithinAt gives the genuine finite identity used in passing to the original infinite transformed ODE.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] solution solutionSlope realSolution realSlope

/-- The actual finite transformed quasi-derivative.
Use: finiteTransformedQuasiDerivative_hasDerivWithinAt gives the genuine finite identity used in passing to the original infinite transformed ODE.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteTransformedQuasiDerivative (a : ℝ) (ha : -1<a) (N : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  finiteTransformedSlope a ha N z t-
    2*(finiteKernelDiagonal a ha N (halfParameterClamp t):ℂ)*finiteTransformedSolution a ha N (halfParameterClamp t) z

/-- The genuine finite quasi-derivative satisfies exactly the original printed identity, with every finite inverse, differentiation and ODE condition discharged.
Use: its integrated form passes the actual finite transformed ODE to the infinite original solution once the genuine first-derivative limit is established.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: differentiate the actual finite diagonal/solution product using their independently proved true derivatives. Substitute the independently proved actual finite transformed ODE; its finite diagonal derivative cancels exactly. -/
theorem finiteTransformedQuasiDerivative_hasDerivWithinAt (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ (t : HalfInterval) (z : ℂ),0<(t:ℝ) →
      HasDerivWithinAt (finiteTransformedQuasiDerivative a ha N z)
        (((potential a t:ℂ)-z)*finiteTransformedSolution a ha N t z-
          2*(finiteKernelDiagonal a ha N t:ℂ)*finiteTransformedSlope a ha N z t)
        (Icc ((t:ℝ)/2) (1/2)) (t:ℝ) := by
  -- The same actual finite solution and diagonal occur in all three independently proved derivatives.
  filter_upwards [finiteTransformedSolution_ODE a ha,finiteTransformedSolution_hasDerivWithinAt a ha,
    finiteKernelDiagonal_hasDerivWithinAt a ha] with N hODE hU hW t z ht
  have hwd := (hW ((t:ℝ)/2) (by linarith) t (by linarith)).ofReal_comp
  have h := (hODE t z ht).sub ((hwd.const_mul (2:ℂ)).mul (hU t z ht))
  rw [show halfParameterClamp (t:ℝ)=t from Set.projIcc_of_mem (by norm_num) t.property] at h
  change HasDerivWithinAt (finiteTransformedQuasiDerivative a ha N z) _ _ _ at h
  convert h using 1
  push_cast
  ring

/-- A derivative proved on the positive half-point strip also holds on any original positive physical strip containing that point.
Use: the actual finite transformed and quasi-derivative identities can be integrated on arbitrary fixed positive physical subintervals.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: locality of the derivative within a set.
Proof: the half-point lower bound is strictly below the original positive point. Its interval is therefore a neighborhood within every physical strip with the same upper endpoint. -/
theorem hasDerivWithinAt_physicalStrip {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ→E} {v : E} {d : ℝ} (t : HalfInterval) (ht : 0<(t:ℝ))
    (h : HasDerivWithinAt f v (Icc ((t:ℝ)/2) (1/2)) (t:ℝ)) :
    HasDerivWithinAt f v (Icc d (1/2)) (t:ℝ) := by
  apply h.mono_of_mem_nhdsWithin
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith : (t:ℝ)/2<(t:ℝ))),
    self_mem_nhdsWithin] with x hx hs
  exact ⟨hx.le,hs.2⟩

end
end jacobi.GelfandLevitan
