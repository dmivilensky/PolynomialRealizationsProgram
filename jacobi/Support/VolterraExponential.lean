import jacobi.Finite.WeightedVolterraBound
import jacobi.Support.VolterraKernelBounds

/-!
Article: jacobi, Appendix C.3.
The actual original support wave obeys a uniform energy-scaled bound
at every complex spectral parameter. Its exact original Volterra
equation, genuine top-node growth and actual weighted kernel estimates
discharge every premise. This exponential estimate suffices in every
bounded-scaled-energy application of the printed cosh estimate.
Use: bounded-scaled-energy support waves are uniformly controlled for the genuine support edge limit and the transition regime of the original oscillatory envelope.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference jacobi.Finite
open scoped Topology

/-- The actual complex support wave has a uniform energy-scaled exponential bound throughout the original growing half-chain range.
Use: bounded-scaled-energy support waves are uniformly controlled for the genuine support edge limit and the transition regime of the original oscillatory envelope.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the genuine top-node solution has its proved polynomial upper bound and the actual reduction-of-order kernel has its proved uniform weighted linear bound. The original exact complex Volterra identity supplies the true wave equation; the finite-prefix weighted Gronwall theorem then applies to these same actual original objects. -/
theorem naturalWave_exponential {a b : ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C B:ℝ,0<C ∧ 0<B ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,2*m≤n+6→∀y:ℂ,
      ‖naturalWave a b ha hb n m y‖≤C*((m:ℝ)+1)^gamma a*
        exp (B*‖y-(cos (gamma a*step a b (n+1)):ℝ)‖*((m:ℝ)+1)^2) := by
  -- Every original wave and kernel in the generic estimate is the actual reconstructed support spectral family.
  obtain ⟨c,C,hc,hC,hbound⟩ := topValue_bounds ha hb
  obtain ⟨B,hB,hkernel⟩ := volterraKernel_linear ha hb
  refine ⟨C,B,hC,hB,?_⟩
  filter_upwards [hbound,hkernel,eventually_ge_atTop (8:ℕ)] with n hn hk hlarge
  intro m hm y
  let u : ℕ→ℂ := fun j => (topValue a b ha hb n j:ℂ)
  let v := fun j => naturalWave a b ha hb n j y
  let G := volterraKernel a b ha hb n
  let w : ℕ→ℝ := fun j => ((j:ℝ)+1)^gamma a
  let d : ℂ := y-(cos (gamma a*step a b (n+1)):ℝ)
  have hw (j : ℕ) (_hj:j≤m) : 0<w j := rpow_pos_of_pos (by positivity) _
  have hu (j : ℕ) (hj:j≤m) : ‖u j‖≤C*w j := by
    have hp : 0≤topValue a b ha hb n j := (naturalPolynomial_top_pos ha hb (by omega)).le
    simpa only [u,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp] using (hn j (by omega)).2
  have hG (j : ℕ) (hj:j≤m) (k : ℕ) (hkj:k<j) : 0≤G j k ∧ G j k*w k/w j≤B*((j-k:ℕ):ℝ) :=
    ⟨volterraKernel_nonneg ha hb (by omega) (by omega),hk j k (by omega) hkj.le⟩
  have hv (j : ℕ) (hj:j≤m) : v j=u j+d*∑k∈Finset.range j,(G j k:ℂ)*v k :=
    naturalWave_volterra a b ha hb n j (by omega) y
  exact weighted_volterra_bound u v G w d m hC.le hB.le hw hu hG hv

end
end jacobi.Support
