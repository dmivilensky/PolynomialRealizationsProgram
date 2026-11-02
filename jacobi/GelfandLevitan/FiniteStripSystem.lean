import jacobi.GelfandLevitan.FiniteStripData

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The actual original finite GL strip data satisfy the genuine
first-order quasi-derivative system. All continuity totalizations,
finite inverse conditions and spatial derivative assumptions are
discharged from the original finite GL construction.
Use: finiteStripSystem transfers the proved original finite derivatives to their genuine continuous-strip functions without changing physical coordinates.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Restricting a genuine derivative to its identical physical strip values preserves the actual derivative.
Use: finiteStripSystem transfers the proved original finite derivatives to their genuine continuous-strip functions without changing physical coordinates.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: locality of the derivative within a set.
Proof: the original strip clipping fixes each physical point, so the continuous extension and the original function agree on the full derivative domain and at its base point. -/
theorem stripDerivative_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : ℝ} (hpq : p≤q) (g : C(ClosedStrip p q,E)) (f : ℝ→E)
    (he : ∀ t : ClosedStrip p q,g t=f t) (t : ClosedStrip p q) {v : E}
    (hD : HasDerivWithinAt f v (Icc p q) (t:ℝ)) :
    HasDerivWithinAt (stripExtension hpq g) v (Icc p q) (t:ℝ) := by
  apply hD.congr
  · intro x hx
    change g (Set.projIcc p q hpq x)=f x
    rw [Set.projIcc_of_mem hpq hx]
    exact he ⟨x,hx⟩
  · rw [stripExtension_value]
    exact he t

/-- Every sufficiently long actual finite GL approximation satisfies the genuine first-order quasi-derivative system on every fixed positive physical strip, at every complex energy.
Use: the general closed-system limit theorem applies to the original finite diagonals and transformed solutions without any unproved ODE or derivative-limit premise.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the actual finite strip values are independently identified with the original finite GL functions. Their original genuine solution derivative and app-quasi identity are already proved. Restrict them to the same physical strip and substitute the defining actual quasi-derivative; the displayed first-order system is exact algebra. -/
theorem finiteStripSystem (a : ℝ) (ha : -1<a) {d : ℝ} (hd : 0<d) (hds : d<(1/2:ℝ)) :
    ∀ᶠ N : ℕ in atTop,∀ z : ℂ,
      (∀ t : ClosedStrip d (1/2),
        HasDerivWithinAt (stripExtension hds.le (finiteSolutionStrip a ha N d z))
          (2*(finiteDiagonalStrip a ha N d t:ℂ)*finiteSolutionStrip a ha N d z t+finiteQuasiStrip a ha N d z t)
          (Icc d (1/2)) (t:ℝ)) ∧
      (∀ t : ClosedStrip d (1/2),
        HasDerivWithinAt (stripExtension hds.le (finiteQuasiStrip a ha N d z))
          (quasiEquationCoefficient a hd z (finiteDiagonalStrip a ha N d) t*finiteSolutionStrip a ha N d z t-
            2*(finiteDiagonalStrip a ha N d t:ℂ)*finiteQuasiStrip a ha N d z t)
          (Icc d (1/2)) (t:ℝ)) := by
  -- All hypotheses of the abstract strip-system limit are discharged by the actual original finite GL calculus.
  filter_upwards [finiteStripData_values a ha hd,finiteTransformedSolution_hasDerivWithinAt a ha,
    finiteTransformedQuasiDerivative_hasDerivWithinAt a ha] with N hVal hU hV z
  have hphysical (t : ClosedStrip d (1/2)) : (t:ℝ)∈Icc (0:ℝ) (1/2) :=
    ⟨(hd.trans_le t.property.1).le,t.property.2⟩
  have hfix (t : ClosedStrip d (1/2)) : halfParameterClamp (t:ℝ)=(⟨(t:ℝ),hphysical t⟩:HalfInterval) :=
    Set.projIcc_of_mem (by norm_num) (hphysical t)
  constructor
  · intro t
    have hD := hasDerivWithinAt_physicalStrip (d := d) ⟨(t:ℝ),hphysical t⟩ (hd.trans_le t.property.1)
      (hU ⟨(t:ℝ),hphysical t⟩ z (hd.trans_le t.property.1))
    have h := stripDerivative_congr hds.le (finiteSolutionStrip a ha N d z)
      (fun x => finiteTransformedSolution a ha N (halfParameterClamp x) z)
      (fun x => (hVal z x).2.1) t hD
    convert h using 1
    rw [(hVal z t).1,(hVal z t).2.1,(hVal z t).2.2,finiteTransformedQuasiDerivative,hfix]
    ring
  · intro t
    have hD := hasDerivWithinAt_physicalStrip (d := d) ⟨(t:ℝ),hphysical t⟩ (hd.trans_le t.property.1)
      (hV ⟨(t:ℝ),hphysical t⟩ z (hd.trans_le t.property.1))
    have h := stripDerivative_congr hds.le (finiteQuasiStrip a ha N d z)
      (finiteTransformedQuasiDerivative a ha N z) (fun x => (hVal z x).2.2) t hD
    convert h using 1
    change (((potential a t:ℂ)-z-4*(finiteDiagonalStrip a ha N d t:ℂ)*(finiteDiagonalStrip a ha N d t:ℂ))*
      finiteSolutionStrip a ha N d z t-2*(finiteDiagonalStrip a ha N d t:ℂ)*finiteQuasiStrip a ha N d z t)=_
    rw [(hVal z t).1,(hVal z t).2.1,(hVal z t).2.2,finiteTransformedQuasiDerivative,hfix]
    ring

end
end jacobi.GelfandLevitan
