import jacobi.Support.NormalizedKernelLimit
import jacobi.Support.ContinuumVolterra
import jacobi.Analysis.BoundedDoubleMesh

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
The actual normalized finite Volterra operator and its fixed-rectangle
mesh representation. The limiting rectangle integral is computed as
twice the genuine nested continuum operator; no formal interchange of
singular improper integrals is assumed.
Use: finiteGroundMesh_integral represents this original finite double sum exactly, and finiteGroundMesh_limit passes it to twice groundVolterra in the complex support edge proof.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter Finset MeasureTheory jacobi.Reference
open scoped Topology

/-- The actual degree-normalized nested finite ground operator.
Use: finiteGroundMesh_integral represents this original finite double sum exactly, and finiteGroundMesh_limit passes it to twice groundVolterra in the complex support edge proof.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
-/
def finiteGroundMesh (a b:ℝ) (ha:-1<a) (hb:-1<b) (n m:ℕ) (q:ℝ→ℂ) : ℂ :=
  (∑l∈range m,∑j∈range (l+1),(normalizedKernel a b ha hb n l j:ℂ)*q ((j:ℝ)/(n:ℝ)))/(n:ℂ)^2

/-- The original normalized finite operator extended by zero outside its actual triangular mesh prefix.
Use: finiteGroundMesh_integral integrates this genuine finite data on a fixed unit square; normalizedKernel_bound gives one constant dominating its entire zero extension.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
-/
def groundMeshData (a b:ℝ) (ha:-1<a) (hb:-1<b) (n m:ℕ) (q:ℝ→ℂ) (l j:ℕ) : ℂ :=
  if l<m ∧ j≤l then (normalizedKernel a b ha hb n l j:ℂ)*q ((j:ℝ)/(n:ℝ)) else 0

/-- The zero extension of a genuine finite prefix has precisely its original finite sum.
Use: finiteGroundMesh_integral computes both original triangular index cutoffs before applying the exact complex mesh integral theorem.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Source: finite sums extended by zero.
Proof: extend the smaller range to the larger one; every newly included index has its actual cutoff false. -/
theorem sum_range_cutoff (f:ℕ→ℂ) {m n:ℕ} (hm:m≤n) :
    (∑j∈range n,if j<m then f j else 0)=∑j∈range m,f j := by
  -- Newly added indices have zero value, so extension preserves the original finite sum.
  classical
  symm
  calc
    _ = ∑j∈range m,if j<m then f j else 0 := by
      apply sum_congr rfl
      intro j hj
      rw [ite_eq_left (Finset.mem_range.mp hj)]
    _ = _ := sum_subset (range_mono hm) (by
      intro j _ hj
      exact ite_eq_right (by simpa only [Finset.mem_range] using hj))

/-- The original normalized finite Volterra sum equals the integral of its actual bounded double mesh.
Use: finiteGroundMesh_limit applies bounded double-mesh convergence to the original support kernel, including its true moving terminal prefix.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: integrate both actual mesh coordinates exactly. The outer cutoff leaves precisely the original m rows, and the inner cutoff leaves precisely their original l+1 columns. -/
theorem finiteGroundMesh_integral (a b:ℝ) (ha:-1<a) (hb:-1<b)
    {n m:ℕ} (hn:0<n) (hm:m≤n) (q:ℝ→ℂ) :
    (∫r in (0:ℝ)..1,∫s in (0:ℝ)..1,
      groundMeshData a b ha hb n m q (Nat.floor ((n:ℝ)*r)) (Nat.floor ((n:ℝ)*s)))=
      finiteGroundMesh a b ha hb n m q := by
  -- Both original triangular cutoffs are retained in the same actual finite data.
  rw [jacobi.Analysis.double_mesh_integral n _ hn]
  unfold finiteGroundMesh
  congr 1
  -- The outer zero extension keeps exactly the original terminal prefix.
  have hout : (∑l∈range n,∑j∈range n,groundMeshData a b ha hb n m q l j)=
      ∑l∈range n,if l<m then
        (∑j∈range n,if j<l+1 then (normalizedKernel a b ha hb n l j:ℂ)*q ((j:ℝ)/(n:ℝ)) else 0) else 0 := by
    apply sum_congr rfl
    intro l _
    by_cases hl:l<m
    · simp only [groundMeshData,hl,true_and,ite_eq_left,show ∀j:ℕ,j≤l↔j<l+1 from fun j => by omega]
    · simp only [groundMeshData,hl,false_and,ite_false,sum_const_zero]
  rw [hout,sum_range_cutoff _ hm]
  apply sum_congr rfl
  intro l hl
  exact sum_range_cutoff _ (by have := Finset.mem_range.mp hl; omega)

/-- The actual fixed-rectangle continuum kernel in normalized ground coordinates.
Use: groundRectangle_integral identifies the limiting double mesh with twice the genuine groundVolterra operator solved by regularWave.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
-/
def groundRectangle (a:ℝ) (q:ℝ→ℂ) (t r s:ℝ) : ℂ :=
  if r≤t then if s≤r then (2*(weight a s:ℂ)^2/(weight a r:ℂ)^2)*q s else 0 else 0

/-- Integrating the actual continuum rectangle gives exactly twice the original normalized nested ground operator.
Use: finiteGroundMesh_limit identifies the genuine continuum value of the original double mesh, with its factor two coming from the actual coupling limit one half.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the inner interval indicator cuts the unit interval to 0..r. Pull its actual constant denominator and factor two through that integral. The outer indicator then cuts 0..1 to 0..t, giving exactly the original nested ground operator. -/
theorem groundRectangle_integral (a:ℝ) (q:ℝ→ℂ) {t:ℝ} (ht:t∈Icc (0:ℝ) (1/2)) :
    (∫r in (0:ℝ)..1,∫s in (0:ℝ)..1,groundRectangle a q t r s)=2*groundVolterra a q t := by
  -- Each interval cutoff is handled by the ordinary exact indicator integral theorem.
  have hi (r:ℝ) (hr:r∈Icc (0:ℝ) t) :
      (∫s in (0:ℝ)..1,groundRectangle a q t r s)=2*groundFlux a q r := by
    simp only [groundRectangle,ite_eq_left hr.2]
    change (∫s in (0:ℝ)..1,({s:ℝ | s≤r}.indicator
      (fun s => (2*(weight a s:ℂ)^2/(weight a r:ℂ)^2)*q s)) s)=_
    rw [intervalIntegral.integral_indicator ⟨hr.1,by linarith [hr.2,ht.2]⟩]
    have he : (fun s:ℝ => (2*(weight a s:ℂ)^2/(weight a r:ℂ)^2)*q s)=
        fun s => 2*((weight a s:ℂ)^2*q s)/(weight a r:ℂ)^2 := by funext s; ring
    rw [he,intervalIntegral.integral_div,intervalIntegral.integral_const_mul,groundFlux]
    ring
  have ho : (∫r in (0:ℝ)..1,∫s in (0:ℝ)..1,groundRectangle a q t r s)=
      ∫r in (0:ℝ)..1,({r:ℝ | r≤t}.indicator (fun r => 2*groundFlux a q r)) r := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hr
    by_cases hrt:r≤t
    · simpa only [indicator_of_mem (show r∈{r:ℝ | r≤t} from hrt)] using hi r ⟨hr.1,hrt⟩
    · simp [groundRectangle,hrt]
  rw [ho,intervalIntegral.integral_indicator ⟨ht.1,by linarith [ht.2]⟩,
    intervalIntegral.integral_const_mul,groundVolterra]

end
end jacobi.Support
