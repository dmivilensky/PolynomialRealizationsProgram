import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
The exact degree/matrix-dimension ratio tends to one along every
cofinal sequence. Both mesh coordinates therefore have the same
moving-index limit, including the physical zero and midpoint.
Source: elementary limits of natural-number mesh ratios.
Use: degree_to_size_mesh and size_to_degree_mesh transfer the spatial coordinates in the original finite edge, uniform Gram and eigenvector proofs.
-/
namespace jacobi.Analysis
noncomputable section
open Filter
open scoped Topology

/-- The actual matrix dimension divided by its original degree tends to one along every cofinal index filter.
Use: degree_to_size_mesh and size_to_degree_mesh transfer the spatial coordinates in the original finite edge, uniform Gram and eigenvector proofs.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the exact ratio is 1+1/n once the genuine cofinal degree is positive. -/
theorem successor_ratio_tendsto {ι:Type*} {l:Filter ι} {n:ι→ℕ} (hn:Tendsto n l atTop) :
    Tendsto (fun i => ((n i:ℝ)+1)/(n i:ℝ)) l (𝓝 1) := by
  have h := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hn).const_add 1
  simp only [add_zero] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [hn.eventually_gt_atTop 0] with i hi
  have hn0 : (n i:ℝ)≠0 := by exact_mod_cast hi.ne'
  dsimp only [Function.comp_def]
  field_simp [hn0]

/-- A degree mesh and the corresponding true matrix-size mesh have the same limit along every cofinal sequence.
Use: the uniform Gram proof evaluates the original continuous kernels on the true matrix half square while reusing the actual degree-normalized polynomial limits.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: divide the genuine degree mesh by the exact matrix-dimension ratio, whose limit is one. -/
theorem degree_to_size_mesh {ι:Type*} {l:Filter ι} {n m:ι→ℕ} {t:ℝ}
    (hn:Tendsto n l atTop) (hm:Tendsto (fun i => (m i:ℝ)/(n i:ℝ)) l (𝓝 t)) :
    Tendsto (fun i => (m i:ℝ)/((n i:ℝ)+1)) l (𝓝 t) := by
  have h := hm.div (successor_ratio_tendsto hn) one_ne_zero
  simp only [div_one] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [hn.eventually_gt_atTop 0] with i hi
  have hn0 : (n i:ℝ)≠0 := by exact_mod_cast hi.ne'
  change (m i:ℝ)/((n i:ℝ)+1)=((m i:ℝ)/(n i:ℝ))/(((n i:ℝ)+1)/(n i:ℝ))
  field_simp [hn0]

/-- A true matrix-size mesh and its corresponding original degree mesh have the same limit along every cofinal sequence.
Use: half_matrix_uniform_zero obtains compactness in the exact closed physical matrix half square and then applies the actual polynomial and Gram limits in the original degree coordinate.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: multiply the genuine matrix-size mesh by the exact dimension/degree ratio, which tends to one. -/
theorem size_to_degree_mesh {ι:Type*} {l:Filter ι} {n m:ι→ℕ} {t:ℝ}
    (hn:Tendsto n l atTop) (hm:Tendsto (fun i => (m i:ℝ)/((n i:ℝ)+1)) l (𝓝 t)) :
    Tendsto (fun i => (m i:ℝ)/(n i:ℝ)) l (𝓝 t) := by
  have h := hm.mul (successor_ratio_tendsto hn)
  simp only [mul_one] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [hn.eventually_gt_atTop 0] with i hi
  have hn0 : (n i:ℝ)≠0 := by exact_mod_cast hi.ne'
  field_simp [hn0]

end
end jacobi.Analysis
