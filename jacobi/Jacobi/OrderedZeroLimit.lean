import jacobi.Jacobi.FiniteZeroStability
import jacobi.Bessel.OrderedApproximation

/-!
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
The actual canonically ordered finite Jacobi squared zeros converge to
the complete original Bessel zero sequence. All zero-stability inputs
are proved for the same genuine polynomial family. The ordering proof
is shared with the Laguerre counterexample through OrderedApproximation.
Use: the full fixed-index spectral assertion of Lemma spec, with both the finite and limiting zero orderings proved complete.
-/
namespace jacobi.Jacobi
noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Every original canonically ordered finite squared Jacobi zero converges to the corresponding actual Bessel spectral zero.
Use: the full fixed-index spectral assertion of Lemma spec, with both the finite and limiting zero orderings proved complete.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: actual positive finite ordering, real zero existence, compact
gap exclusion and complex local injectivity discharge every input to
the shared ordered-zero theorem. Its padding is exactly the original
finiteSigmaAt definition, so no finite index or source zero is replaced. -/
theorem finiteSigmaAt_tendsto {a b:ℝ} (ha:-1 < a) (hb:-1 < b) (k:ℕ) :
    Tendsto (fun n:ℕ=>finiteSigmaAt a b ha hb n k) atTop
      (𝓝 (jacobi.Bessel.sigma a ha k)) := by
  -- The actual finite and limiting objects are those already used throughout the original Jacobi spectral proof.
  have h:= jacobi.Bessel.ordered_zero_limit ha (finiteSigma a b ha hb)
    (fun n z=>normalized (a:ℂ) (b:ℂ) n (1-z/(2*(n:ℂ)^2)))
    (fun n=>⟨fun i=>(finiteSigma_properties ha hb (by have hh:=i.isLt; omega)).1 i,
      fun i j hij=>(finiteSigma_properties ha hb (by have hh:=i.isLt; omega)).2 hij⟩)
    (fun n i=>finiteSigma_is_zero ha hb (by have hh:=i.isLt; omega) i)
    (fun j e he=>finiteSigma_approximation ha hb (jacobi.Bessel.sigma_mem ha j) he)
    (fun _ _ hg=>finite_zero_exclusion_interval (b:=b) ha hg)
    (fun j=>scaled_injective_near_zero (b:=(b:ℂ)) (by simpa using ha) (jacobi.Bessel.sigma_mem ha j)) k
  exact h

end
end jacobi.Jacobi
