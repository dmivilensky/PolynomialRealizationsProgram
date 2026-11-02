import jacobi.Finite.ReductionKernelBound
import jacobi.Support.CoefficientBounds
import jacobi.Support.TopUniformLimit

/-!
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
All original matrix, polynomial and positivity inputs are discharged.
Use: the complex support-wave bound and the original support edge limit have uniform weighted kernels and a bounded dominating function without splitting the singular endpoint exponent into cases.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference jacobi.Finite
open scoped Topology

/-- The genuine support reduction-of-order kernel has a uniform linear Volterra majorant after the actual original growth weights are applied.
Use: the complex support-wave bound and the original support edge limit have uniform weighted kernels and a bounded dominating function without splitting the singular endpoint exponent into cases.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the actual top-node solution has proved positive two-sided polynomial growth and every actual original matrix coupling has a uniform positive lower bound. The genuine growth weight is positive and monotone. Apply the proved elementary reduction-of-order bound to these same original objects on each actual finite prefix. -/
theorem volterraKernel_linear {a b : ℝ} (ha:-1<a) (hb:-1<b) :
    ∃B:ℝ,0<B ∧ ∀ᶠn:ℕ in atTop,∀m j:ℕ,2*m≤n+6→j≤m→
      volterraKernel a b ha hb n m j*((j:ℝ)+1)^gamma a/((m:ℝ)+1)^gamma a≤B*((m-j:ℕ):ℝ) := by
  -- The original kernel and matrix are retained exactly; the generic weighted bound has no remaining support assumptions.
  obtain ⟨c,C,hc,hC,hbound⟩ := topValue_bounds ha hb
  obtain ⟨A,D,hA,hD,hcoeff⟩ := coefficient_bounds ha hb
  have hg := (parameter_pos ha hb).1.le
  refine ⟨C^2/(A*c^2),by positivity,?_⟩
  filter_upwards [hbound,(tendsto_add_atTop_nat 1).eventually hcoeff] with n hn he
  intro m j hm hj
  let u := topValue a b ha hb n
  let ac : ℕ→ℝ := fun r => sqrt ((naturalChain a b ha hb (n+1)).data.aSq r)
  let w : ℕ→ℝ := fun r => ((r:ℝ)+1)^gamma a
  have hw (r : ℕ) (_hr:r≤m) : 0<w r := rpow_pos_of_pos (by positivity) _
  have hmono (r s : ℕ) (hrs:r≤s) (_hs:s≤m) : w r≤w s := by
    apply Real.rpow_le_rpow (by positivity) _ hg
    exact_mod_cast Nat.add_le_add_right hrs 1
  have hu (r : ℕ) (hr:r≤m) : c*w r≤u r ∧ u r≤C*w r := hn r (by omega)
  have hac (r : ℕ) (hr:r<m) : A≤ac (r+1) := (he.2 (r+1) (by omega) (by omega)).1
  exact reduction_kernel_linear u ac w m hc hC hA hw hmono hu hac le_rfl hj

end
end jacobi.Support
