import jacobi.Finite.PaddedClosedSpectrum
import jacobi.Applications.NesterovFull
import jacobi.Jacobi.FibreLimit
import jacobi.Variational.QuarterTransfer

/-!
Full l1 Green-spectrum convergence for the padded Nesterov polynomial.
The active Jacobi roots have their exact full-degree scaling; all repeated
minus-one roots contribute a vanishing, explicitly evaluated spectral mass.
The existing nonnegative Scheffe theorem controls the whole infinite tail.
Use: AllThreeTerm applies closed-fibre transfer to every realization,
including arbitrary restarts and interleavings of the endpoint roots.
Article: jacobi, Theorem 5.3.
Article role: the full repeated-root spectrum and its quarter-scaled l1 edge limit.
-/
namespace jacobi.Applications
noncomputable section
open Real Filter Set jacobi.Jacobi jacobi.Finite jacobi.Variational
open chebyshev2.Continuum
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The full degree in a fixed Nesterov parity, including Landweber roots.
Article: jacobi, Theorem 5.3.
-/
def nesterovParityDimension (e m : ℕ) : ℕ := m+(m+1+e)

/-- The literal interior Jacobi roots followed by all repeated endpoint
roots of the full residual, in the original descending order.
Article: jacobi, Theorem 5.3.
-/
def nesterovParityNodes (a : ℝ) (ha : -1<a) (e m : ℕ) :
    ClosedNodes (nesterovParityDimension e m) :=
  (nodes a ((e:ℝ)-1/2) ha (by linarith [Nat.cast_nonneg (α := ℝ) e]) m).padMinusOne (m+1+e)

/-- The active degree occupies asymptotically half of the full horizon.
Article: jacobi, Theorem 5.3.
-/
theorem nesterov_real_degree_ratio (e : ℕ) :
    Tendsto (fun m : ℕ => (m:ℝ)/(nesterovParityDimension e m:ℝ)) atTop (𝓝 (1/2:ℝ)) := by
  have h := ((count_degree_ratio e).inv₀ (by norm_num : (1:ℝ)≠0)).const_mul (1/2:ℝ)
  norm_num only [inv_one,mul_one] at h
  convert h using 1
  funext m
  rw [inv_div]
  dsimp only [nesterovParityDimension]
  push_cast
  ring

/-- Every fixed active eigenvalue has the exact full-degree normalization.
This identity concerns the actual sorted closed-fibre matrix spectrum.
Article: jacobi, Theorem 5.3.
-/
theorem nesterovParity_spectrum_coordinate {a : ℝ} (ha : -1<a) (e : ℕ)
    {m j : ℕ} (hj : j < m) :
    closedFibreSpectrum (nesterovParityNodes a ha e m) j=
      ((m:ℝ)/(nesterovParityDimension e m:ℝ))^2*
        finiteLambdaAt a ((e:ℝ)-1/2) ha (by linarith [Nat.cast_nonneg (α := ℝ) e]) m j := by
  rw [nesterovParityNodes,Nodes.padMinusOne_spectrum _ hj,
    finiteLambdaAt_eq ha (by linarith [Nat.cast_nonneg (α := ℝ) e]) hj,finiteLambda_node ha (by linarith [Nat.cast_nonneg (α := ℝ) e])]
  have hm : (m:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  dsimp only [nesterovParityDimension]
  field_simp

/-- The full repeated-root trace is the scaled active Jacobi trace plus
the exact endpoint-root trace. No tail bound is assumed.
Article: jacobi, Theorem 5.3.
-/
theorem nesterovParity_spectrum_mass {a : ℝ} (ha : -1<a) (e m : ℕ) :
    (∑' j,closedFibreSpectrum (nesterovParityNodes a ha e m) j)=
      ((m:ℝ)/(nesterovParityDimension e m:ℝ))^2*
        (∑ i : Fin m,finiteLambda a ((e:ℝ)-1/2) ha (by linarith [Nat.cast_nonneg (α := ℝ) e]) m i)+
      (1-(m:ℝ)/(nesterovParityDimension e m:ℝ))/(2*(nesterovParityDimension e m:ℝ)) := by
  rw [nesterovParityNodes,Nodes.padMinusOne_sum,Finset.sum_div,Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [finiteLambda_node ha (by linarith [Nat.cast_nonneg (α := ℝ) e])]
    have hm : (m:ℝ)≠0 := Nat.cast_ne_zero.mpr (by have := i.isLt; omega)
    dsimp only [nesterovParityDimension]
    field_simp
  · have hN : (nesterovParityDimension e m:ℝ)≠0 := Nat.cast_ne_zero.mpr (by
      dsimp [nesterovParityDimension]
      omega)
    change (m+1+e:ℕ)/(2*(nesterovParityDimension e m:ℝ)^2)=_
    field_simp
    dsimp only [nesterovParityDimension]
    push_cast
    ring

/-- Every fixed parity of the full Nesterov polynomial has the entire
quarter-scaled Bessel spectrum as its actual l1 limit. Repeated roots are
included in the proof, rather than omitted before spectral transfer.
Article: jacobi, Theorem 5.3.
-/
theorem nesterovParity_spectral_limit {a : ℝ} (ha : -1<a) (e : ℕ) :
    Tendsto (fun m : ℕ => distance (closedFibreSpectrum (nesterovParityNodes a ha e m))
      (quarterEdge (jacobi.Bessel.edgeSpectrum a ha)).value) atTop (𝓝 0) := by
  let Λ := quarterEdge (jacobi.Bessel.edgeSpectrum a ha)
  have hs m : Summable (closedFibreSpectrum (nesterovParityNodes a ha e m)) :=
    (matrixSpectralData _ (normalizedGreen_posSemidef_of_posDef
      ((nesterovParityNodes a ha e m).endpoint_posDef
        (nesterovParityNodes a ha e m).diagonalChain_mem))).eigenvalue_summable
  have hn m j : 0≤closedFibreSpectrum (nesterovParityNodes a ha e m) j :=
    (matrixSpectralData _ (normalizedGreen_posSemidef_of_posDef
      ((nesterovParityNodes a ha e m).endpoint_posDef
        (nesterovParityNodes a ha e m).diagonalChain_mem))).eigenvalue_nonneg j
  apply nonnegative_scheffe hs Λ.summable hn (fun j => (Λ.positive j).le)
  · intro j
    have h := ((nesterov_real_degree_ratio e).pow 2).mul
      (finiteLambdaAt_tendsto ha (by linarith [Nat.cast_nonneg (α := ℝ) e] : -1<(e:ℝ)-1/2) j)
    have he : (1/2:ℝ)^2*jacobi.Bessel.edgeValue a ha j=Λ.value j := by
      dsimp [Λ,quarterEdge,EdgeSpectrum.scale,jacobi.Bessel.edgeSpectrum]
      ring
    rw [he] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop j] with m hm
    exact (nesterovParity_spectrum_coordinate ha e hm).symm
  · simp_rw [nesterovParity_spectrum_mass ha e]
    have hN : Tendsto (fun m : ℕ => nesterovParityDimension e m) atTop atTop := by
      simpa only [nesterovParityDimension,show ∀ m : ℕ,m+(m+1+e)=2*m+1+e from fun _ => by omega]
        using iterationCount_tendsto e
    have hi := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hN
    have htail := ((tendsto_const_nhds (x := (1:ℝ))).sub (nesterov_real_degree_ratio e)).mul hi
    have h := (((nesterov_real_degree_ratio e).pow 2).mul
      (finiteLambda_sum_tendsto ha (by linarith [Nat.cast_nonneg (α := ℝ) e] : -1<(e:ℝ)-1/2))).add (htail.div_const 2)
    have hmass : (∑' j,Λ.value j)=(1/4:ℝ)*(1/(2*(a+1))) := by
      change (∑' j,(1/4:ℝ)*(jacobi.Bessel.edgeSpectrum a ha).value j)=_
      rw [tsum_mul_left,← EdgeSpectrum.mass,jacobi.Bessel.edgeSpectrum_mass ha]
    rw [hmass]
    convert h using 1
    · funext m
      dsimp only [Function.comp_def]
      ring
    · ring

/-- Transport a root list across an exact dimension equality. The
transport changes no polynomial roots or sorted spectral values.
Article: jacobi, Theorem 5.3.
-/
def castClosedNodes {N M : ℕ} (h : N=M) (S : ClosedNodes N) : ClosedNodes M := h ▸ S

/-- Dimension transport leaves the actual common spectral sequence unchanged.
Article: jacobi, Theorem 5.3.
-/
theorem castClosedNodes_spectrum {N M : ℕ} (h : N=M) (S : ClosedNodes N) :
    closedFibreSpectrum (castClosedNodes h S)=closedFibreSpectrum S := by
  subst M
  rfl

/-- The complete Nesterov root list at the positive horizon n+1, with
the actual parity n mod 2 and all repeated endpoint roots included.
Article: jacobi, Theorem 5.3.
-/
def nesterovClosedNodes (a : ℝ) (ha : -1<a) (n : ℕ) : ClosedNodes (n+1) :=
  castClosedNodes (by unfold nesterovParityDimension; omega)
    (nesterovParityNodes a ha (n%2) (n/2))

/-- The full horizon and the parity parametrization have exactly the
same spectrum, before taking any asymptotic limit.
Article: jacobi, Theorem 5.3.
-/
theorem nesterovClosed_spectrum_eq (a : ℝ) (ha : -1<a) (n : ℕ) :
    closedFibreSpectrum (nesterovClosedNodes a ha n)=
      closedFibreSpectrum (nesterovParityNodes a ha (n%2) (n/2)) :=
  castClosedNodes_spectrum _ _

/-- The actual full sequence of padded Nesterov spectra converges in l1
to the quarter edge. Both parity subsequences and every repeated root
are retained; the result applies to the entire closed polynomial fibre.
Article: jacobi, Theorem 5.3.
-/
theorem nesterovClosed_spectral_limit {a : ℝ} (ha : -1<a) :
    Tendsto (fun n : ℕ => distance (closedFibreSpectrum (nesterovClosedNodes a ha n))
      (quarterEdge (jacobi.Bessel.edgeSpectrum a ha)).value) atTop (𝓝 0) := by
  have hm : Tendsto (fun n : ℕ => n/2) atTop atTop :=
    le_of_eq (map_div_atTop_eq_nat 2 (by omega))
  have h := tendsto_parity_choice
    (fun e n => distance (closedFibreSpectrum (nesterovParityNodes a ha e (n/2)))
      (quarterEdge (jacobi.Bessel.edgeSpectrum a ha)).value)
    (fun n => n%2) (fun n => by omega)
    ((nesterovParity_spectral_limit ha 0).comp hm)
    ((nesterovParity_spectral_limit ha 1).comp hm)
  simpa only [nesterovClosed_spectrum_eq] using h

end
end jacobi.Applications
