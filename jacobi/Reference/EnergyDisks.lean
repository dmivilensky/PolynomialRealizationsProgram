import jacobi.Reference.Solutions

/-!
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
The actual complex square-root frequency above a unit disk about a
large positive shifted real energy stays in a fixed imaginary strip
and retains its genuine frequency scale. These explicit geometric
bounds transfer the source frequency estimate to energy Cauchy circles.
Use: supplies all genuine frequency premises on the original energy Cauchy circles in the GL kernel estimate.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- A unit perturbation of a sufficiently positive real energy retains its true square-root frequency scale and has imaginary frequency at most one.
Use: supplies all genuine frequency premises on the original energy Cauchy circles in the GL kernel estimate.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: the perturbed real part is at least E-1 and its norm at most E+1.
The actual square root has norm square equal to that norm and real square
minus imaginary square equal to that real part. Their difference bounds
the imaginary square by one, while the real-part lower bound gives the
required true frequency scale. -/
theorem sqrt_positive_energy_disk {E r : ℝ} (hr : 1≤r) (hE : r^2+1≤E)
    {z : ℂ} (hz : ‖z-(E:ℂ)‖≤1) :
    r≤‖Complex.sqrt z‖ ∧ |(Complex.sqrt z).im|≤1 := by
  -- Only the actual square-root square is used, so branch-cut conventions do not enter the estimate.
  have hrp : 0<r := lt_of_lt_of_le zero_lt_one hr
  have hEp : 0<E := by nlinarith
  have hre := (Complex.abs_re_le_norm (z-(E:ℂ))).trans hz
  have hrez : E-1≤z.re := by
    simp only [sub_re,ofReal_re] at hre
    linarith [(abs_le.mp hre).1]
  have hnorm : ‖z‖≤E+1 := by
    have hh := norm_add_le (z-(E:ℂ)) (E:ℂ)
    rw [sub_add_cancel,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hEp] at hh
    linarith
  have hns : ‖Complex.sqrt z‖^2=‖z‖ := by
    rw [← norm_pow,frequency_square]
  have hcoords : (Complex.sqrt z).re^2+(Complex.sqrt z).im^2=‖z‖ := by
    rw [← hns,← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    ring
  have hs := congrArg Complex.re (frequency_square z)
  simp only [pow_two,mul_re] at hs
  have him2 : (Complex.sqrt z).im^2≤1 := by nlinarith
  constructor
  · have hh : z.re≤‖z‖ := Complex.re_le_norm z
    nlinarith [norm_nonneg (Complex.sqrt z)]
  · exact (sq_le_sq₀ (abs_nonneg _) zero_le_one).mp (by simpa only [sq_abs,one_pow] using him2)

/-- The actual reference energy square root stays in a fixed imaginary strip and above its prescribed real scale on the original unit energy disk.
Use: applies the actual source high-frequency reference bound to every point of the energy Cauchy circle.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: subtract the same original fixed potential shift from the energy and disk center, then use the proved genuine positive-energy square-root estimate. -/
theorem reference_energy_disk {a E r : ℝ} (hr : 1≤r)
    (hE : r^2+1≤E- jacobi.Jacobi.endpointCorrection a) {z : ℂ}
    (hz : z∈Metric.closedBall (E:ℂ) 1) :
    r≤‖Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))‖ ∧
      |(Complex.sqrt (z-(jacobi.Jacobi.endpointCorrection a:ℂ))).im|≤1 := by
  apply sqrt_positive_energy_disk hr hE
  have hh : ‖z-(E:ℂ)‖≤1 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  convert hh using 1
  congr 1
  push_cast
  ring

end
end jacobi.Reference
