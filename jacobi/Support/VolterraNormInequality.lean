import jacobi.Finite.WeightedVolterraInequality
import jacobi.Support.VolterraKernelBounds

/-!
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
The genuine original support wave satisfies a uniform positive weighted
linear-kernel norm inequality at every complex energy. This is the
single actual support input for the global cosh and local error bounds.
Use: naturalWave_cosh and the original Volterra error bounds apply the proved finite positive comparison to this same actual wave without assuming any recurrence or kernel certificate.
-/
namespace jacobi.Support
noncomputable section
open Real Filter jacobi.Reference jacobi.Finite
open scoped Topology

/-- The actual complex support wave obeys the genuine weighted positive linear-kernel norm inequality throughout the full original growing half chain.
Use: naturalWave_cosh and the original Volterra error bounds apply the proved finite positive comparison to this same actual wave without assuming any recurrence or kernel certificate.
Article: jacobi, Appendix C.3 (discrete Volterra equation and cosh estimates).
Proof: the true top-node solution has its proved original growth bound, the actual reduction-of-order kernel has its proved weighted linear bound, and the genuine complex Volterra identity holds for the original spectral polynomial. Apply the shared finite norm comparison with all these actual inputs. -/
theorem naturalWave_norm_inequality {a b : ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C B:ℝ,0<C ∧ 0<B ∧ ∀ᶠn:ℕ in atTop,∀m:ℕ,2*m≤n+6→∀y:ℂ,
      ‖naturalWave a b ha hb n m y‖/((m:ℝ)+1)^gamma a≤C+
        (‖y-(cos (gamma a*step a b (n+1)):ℝ)‖*B)*
          ∑k∈Finset.range m,((m-k:ℕ):ℝ)*(‖naturalWave a b ha hb n k y‖/((k:ℝ)+1)^gamma a) := by
  -- The shared comparison retains every actual original polynomial, matrix coupling, kernel and positive weight.
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
  exact weighted_volterra_inequality u v G w d m hw hu hG hv m le_rfl

end
end jacobi.Support
