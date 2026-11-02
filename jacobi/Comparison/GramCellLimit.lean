import jacobi.Comparison.CellGramMatrix
import jacobi.Comparison.CellKernelLimit
import jacobi.Comparison.UniformGram

/-!
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
The actual positive cell-compressed comparison matrix approximates the
original Gram perturbation with a uniformly o(1/N) entry error. Both the
original two-edge parity and the N versus N+4 normalization are retained.
Use: cellPerturbation_uniform controls the denominator drift explicitly.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter MeasureTheory jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace

/-- The true cell-compressed matrix uses the physical cell denominator
N+4 times the actual averaged kernels, with the original parity sign.
Use: cellPerturbation_uniform controls the denominator drift explicitly.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: each rectangle has area (2/(N+4))^2 and the original form is
multiplied by (N+4)/4; the displayed reciprocal follows by real algebra. -/
theorem cellPerturbation_average (a b:ℝ) (ha:-1<a) (hb:-1<b)
    (n:ℕ) (i j:Fin (n+1)) :
    cellPerturbation a b ha hb n i j =
      (averagedKernel (kernelMap a ha) n i j+
        (-1:ℝ)^(i.val+j.val)*averagedKernel (kernelMap b hb) n i j)/((n:ℝ)+5) := by
  unfold cellPerturbation averagedKernel
  have hM : (n:ℝ)+5≠0 := by positivity
  field_simp
  ring

/-- On the true physical half square, kernelMap at the actual matrix
points is exactly the source kernel at the original matrix coordinates.
Use: the continuum cell-average approximation and the actual spectral
Gram approximation refer to the very same original sampled kernels.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: the genuine half-coordinate clamp fixes every physical sample. -/
theorem kernelMap_matrixPoint (a:ℝ) (ha:-1<a) {n:ℕ} (i j:Fin (n+1))
    (hi:2*i.val≤n+1) (hj:2*j.val≤n+1) :
    kernelMap a ha (matrixPoint n i,matrixPoint n j)=
      kernel a ha (matrixMesh n i) (matrixMesh n j) := by
  change kernel a ha (min (matrixMesh n i) (1/2)) (min (matrixMesh n j) (1/2))=_
  rw [min_eq_left (matrixMesh_mem_half hi).2,min_eq_left (matrixMesh_mem_half hj).2]

/-- The actual cell-compressed perturbation has the same full uniform
two-edge kernel limit as the actual original Gram perturbation.
Use: gramCell_uniform makes their entry difference uniformly o(1/N),
allowing the genuine fixed cell-form gap to survive in the original Gram.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: both true cell averages approach the original samples uniformly.
The actual prefactor N/(N+4) is at most one and approaches one; a fixed
compact kernel norm bounds the entire additional denominator error. -/
theorem cellPerturbation_uniform (a b:ℝ) (ha:-1<a) (hb:-1<b) :
    ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, ∀ i j:Fin (n+1),
      2*i.val≤n+1 → 2*j.val≤n+1 →
      |((n:ℝ)+1)*cellPerturbation a b ha hb n i j-
        (kernel a ha (matrixMesh n i) (matrixMesh n j)+
          (-1:ℝ)^(i.val+j.val)*kernel b hb (matrixMesh n i) (matrixMesh n j))|≤ε := by
  -- Separate the cell-averaging error from the actual N/(N+4) denominator drift.
  intro ε hε
  obtain ⟨NA,hA⟩ := averagedKernel_uniform (kernelMap a ha) (ε/4) (by positivity)
  obtain ⟨NB,hB⟩ := averagedKernel_uniform (kernelMap b hb) (ε/4) (by positivity)
  let C : ℝ := ‖kernelMap a ha‖+‖kernelMap b hb‖
  have hlim : Tendsto (fun n:ℕ => (4/((n:ℝ)+5))*C) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right atTop (5:ℝ) tendsto_natCast_atTop_atTop)).mul_const C
  obtain ⟨ND,hD⟩ := eventually_atTop.mp (hlim.eventually (Iio_mem_nhds (by positivity : (0:ℝ)<ε/2)))
  refine ⟨max (max NA NB) ND,fun n hn i j hi hj => ?_⟩
  have hAn := hA n (le_trans (le_trans (le_max_left NA NB) (le_max_left _ ND)) hn) i j hi hj
  have hBn := hB n (le_trans (le_trans (le_max_right NA NB) (le_max_left _ ND)) hn) i j hi hj
  have hDn := hD n (le_trans (le_max_right _ ND) hn)
  rw [kernelMap_matrixPoint a ha i j hi hj] at hAn
  rw [kernelMap_matrixPoint b hb i j hi hj] at hBn
  let A := kernel a ha (matrixMesh n i) (matrixMesh n j)
  let B := kernel b hb (matrixMesh n i) (matrixMesh n j)
  let s : ℝ := (-1)^(i.val+j.val)
  have hs : |s|=1 := by simp [s]
  have hK : |A+s*B|≤C := by
    have hka := (kernelMap a ha).norm_coe_le_norm (matrixPoint n i,matrixPoint n j)
    have hkb := (kernelMap b hb).norm_coe_le_norm (matrixPoint n i,matrixPoint n j)
    rw [kernelMap_matrixPoint a ha i j hi hj,Real.norm_eq_abs] at hka
    rw [kernelMap_matrixPoint b hb i j hi hj,Real.norm_eq_abs] at hkb
    exact (abs_add_le _ _).trans (by rw [abs_mul,hs,one_mul]; exact add_le_add hka hkb)
  have hr : 0≤((n:ℝ)+1)/((n:ℝ)+5) := by positivity
  have hr1 : ((n:ℝ)+1)/((n:ℝ)+5)≤1 := (div_le_one (by positivity)).mpr (by linarith)
  have he : ((n:ℝ)+1)*cellPerturbation a b ha hb n i j-(A+s*B)=
      (((n:ℝ)+1)/((n:ℝ)+5))*
        ((averagedKernel (kernelMap a ha) n i j-A)+s*(averagedKernel (kernelMap b hb) n i j-B))-
      (4/((n:ℝ)+5))*(A+s*B) := by
    rw [cellPerturbation_average]
    dsimp [s]
    field_simp
    ring
  change |((n:ℝ)+1)*cellPerturbation a b ha hb n i j-(A+s*B)|≤ε
  rw [he]
  have herr : |(averagedKernel (kernelMap a ha) n i j-A)+
      s*(averagedKernel (kernelMap b hb) n i j-B)|≤ε/2 :=
    (abs_add_le _ _).trans (by rw [abs_mul,hs,one_mul]; linarith)
  calc
    _ ≤ |(((n:ℝ)+1)/((n:ℝ)+5))*
        ((averagedKernel (kernelMap a ha) n i j-A)+s*(averagedKernel (kernelMap b hb) n i j-B))|+
      |(4/((n:ℝ)+5))*(A+s*B)| := by
        simpa only [abs_neg,sub_eq_add_neg] using abs_add_le
          ((((n:ℝ)+1)/((n:ℝ)+5))*
          ((averagedKernel (kernelMap a ha) n i j-A)+s*(averagedKernel (kernelMap b hb) n i j-B)))
          (-((4/((n:ℝ)+5))*(A+s*B)))
    _ ≤ ε/2+(4/((n:ℝ)+5))*C := by
      rw [abs_mul,abs_of_nonneg hr,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤4/((n:ℝ)+5))]
      exact add_le_add
        ((mul_le_mul_of_nonneg_left herr hr).trans (mul_le_of_le_one_left (by positivity) hr1))
        (mul_le_mul_of_nonneg_left hK (by positivity))
    _ ≤ ε := by linarith

/-- The original Gram perturbation differs from the actual coercive
cell comparison matrix by a uniform o(1/N) entry error on the whole
physical half square.
Use: uniform finite Gram coercivity absorbs this error into the proved
strictly positive genuine two-edge cell-form bound.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: subtract the two independently proved uniform approximations to
the same original two-edge kernel, keeping the original parity exact. -/
theorem gramCell_uniform {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∀ ε:ℝ, 0<ε → ∃ N:ℕ, ∀ n≥N, ∀ i j:Fin (n+1),
      2*i.val≤n+1 → 2*j.val≤n+1 →
      |((n:ℝ)+1)*(gramPerturbation a b ha hb n i j-cellPerturbation a b ha hb n i j)|≤ε := by
  -- Both independent approximations refer to the same actual two-edge kernel samples.
  intro ε hε
  obtain ⟨NG,hG⟩ := gramPerturbation_uniform ha hb (ε/2) (by positivity)
  obtain ⟨NC,hC⟩ := cellPerturbation_uniform a b ha hb (ε/2) (by positivity)
  refine ⟨max NG NC,fun n hn i j hi hj => ?_⟩
  have h1 := hG n ((le_max_left NG NC).trans hn) i j hi hj
  have h2 := hC n ((le_max_right NG NC).trans hn) i j hi hj
  have he : ((n:ℝ)+1)*(gramPerturbation a b ha hb n i j-cellPerturbation a b ha hb n i j)=
      (((n:ℝ)+1)*gramPerturbation a b ha hb n i j-
        (kernel a ha (matrixMesh n i) (matrixMesh n j)+(-1:ℝ)^(i.val+j.val)*kernel b hb (matrixMesh n i) (matrixMesh n j)))-
      (((n:ℝ)+1)*cellPerturbation a b ha hb n i j-
        (kernel a ha (matrixMesh n i) (matrixMesh n j)+(-1:ℝ)^(i.val+j.val)*kernel b hb (matrixMesh n i) (matrixMesh n j))) := by ring
  rw [he]
  have hh := abs_sub_le
    (((n:ℝ)+1)*gramPerturbation a b ha hb n i j)
    (kernel a ha (matrixMesh n i) (matrixMesh n j)+(-1:ℝ)^(i.val+j.val)*kernel b hb (matrixMesh n i) (matrixMesh n j))
    (((n:ℝ)+1)*cellPerturbation a b ha hb n i j)
  rw [abs_sub_comm (kernel a ha (matrixMesh n i) (matrixMesh n j)+
    (-1:ℝ)^(i.val+j.val)*kernel b hb (matrixMesh n i) (matrixMesh n j))] at hh
  have he2 : ( ((n:ℝ)+1)*gramPerturbation a b ha hb n i j-
      (kernel a ha (matrixMesh n i) (matrixMesh n j)+(-1:ℝ)^(i.val+j.val)*kernel b hb (matrixMesh n i) (matrixMesh n j))) -
    (((n:ℝ)+1)*cellPerturbation a b ha hb n i j-
      (kernel a ha (matrixMesh n i) (matrixMesh n j)+(-1:ℝ)^(i.val+j.val)*kernel b hb (matrixMesh n i) (matrixMesh n j))) =
    ((n:ℝ)+1)*gramPerturbation a b ha hb n i j-((n:ℝ)+1)*cellPerturbation a b ha hb n i j := by ring
  rw [he2]
  exact hh.trans (by linarith)

end
end jacobi.Comparison
