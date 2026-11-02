import krylov.Secant.TerminalSearch
import krylov.Reference.FullCycle
import krylov.Reference.EnergyMeasure

/-!
Article: main_krylov, lem:terminal-fibre, the actual nonanticipating terminal data fibre.
Use: construct identical complete pre-correction data for every globally
CG-consistent policy, with true physical probes, reference steps and residuals.
Source: the concrete CG run, its full-frame completion, actual planar operator
sequence and the proved complete-history nonanticipation theorem.
-/

namespace krylov.Secant
noncomputable section
open Matrix krylov.LinearAlgebra krylov.Reference krylov.Methods
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
variable {n : ℕ}

/-- All actual data before the terminal output correction depend only on the total cross coefficient.
Use: any common correction decision is forced by the same complete actual observed past and actual last probe.
Article: main_krylov, lem:terminal-fibre, full data-fibre assertion.
Proof: actual prefix histories equal the static CG history, whose genuine
direction has a positive CG scale. Actual full-frame completion determines
its last gradient. The true physical planar probe and exact line search then
give the common last observation, actual reference step and printed residual. -/
theorem terminal_data_fibre_of_frame (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hbase : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hN : 0<n)
    (ho : Orthonormal ℝ (fun i : Fin (n+1) => canonicalCGUnitStep base g i.val))
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (n+1)))) (hm : CGConsistent m) (x : ℕ → ℝ) :
    let e := canonicalCGUnitStep base g 0
    let h := canonicalCGUnitStep base g n
    let a := ‖canonicalCGStep base g n‖
    let H0 := methodRun m (fun _ => cgOperator base) (fun _ => cgOperator base) g n
    ∃ t : ℝ, t≠0 ∧ ∀ (y z : ℕ → ℝ)
      (B : ℕ → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))),
      let H := methodRun m (fun k => Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ)
        (physicalTerminalSegments base e h x y z n k)) B g n
      let d := m.direction H
      let Z := Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) (physicalTerminalSegments base e h x y z n n) d
      H=H0 ∧
      Z=Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) (metricRoot base)
        (t • (h+(∑ l ∈ Finset.range n, x l) • e)) ∧
      lineLength H.gradient d Z • d=cgStep base g n ∧
      Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) (metricRoot base)⁻¹ (searchedGradient H.gradient d Z)=
        ((∑ l ∈ Finset.range n, x l)*a) • e := by
  -- The direction scale is selected once on the actual static history and is independent of both hidden diagonals.
  dsimp only
  let e := canonicalCGUnitStep base g 0
  let h := canonicalCGUnitStep base g n
  let a := ‖canonicalCGStep base g n‖
  let H0 := methodRun m (fun _ => cgOperator base) (fun _ => cgOperator base) g n
  obtain ⟨scale, hscale, hdir, _⟩ := hm (cgOperator base) (cgOperator_positive base hbase).1
    (cgOperator_positive base hbase).2 g n
  have hs : canonicalCGStep base g n≠0 := by
    intro hz
    exact ho.ne_zero (Fin.last n) (by simp only [canonicalCGUnitStep, Fin.val_last, hz, NormedSpace.normalize_zero_eq_zero])
  have ha : 0<a := norm_pos_iff.mpr hs
  have halpha := cgLine_ne_zero base g n hs
  let t := scale*(cgLine base g n)⁻¹*a
  have ht : t≠0 := mul_ne_zero (mul_ne_zero hscale.ne' (inv_ne_zero halpha)) ha.ne'
  have hstep : canonicalCGStep base g n=a • h := (NormedSpace.norm_smul_normalize _).symm
  have hd : Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) (metricRoot base) (m.direction H0)=t • h := by
    rw [hdir, map_smul, canonicalCG_direction base g n hs, hstep, smul_smul, smul_smul]
  have hg : Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) (metricRoot base)⁻¹ H0.gradient= -a • h := by
    rw [quadratic_gradient_eq_cg m hm _ (cgOperator_positive base hbase).1 (cgOperator_positive base hbase).2]
    exact canonicalCG_last_gradient base hbase g ho
  have hh : ‖h‖=1 := ho.norm_eq_one (Fin.last n)
  have heh : inner ℝ e h=0 := ho.inner_eq_zero (i := 0) (j := Fin.last n)
    (by intro hz; have hv := congrArg Fin.val hz; simp only [Fin.val_zero, Fin.val_last] at hv; omega)
  refine ⟨t, ht, ?_⟩
  intro y z B
  have hp := terminal_method_prefix base hbase g n hN ho m hm x y z B n le_rfl
  rw [hp]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp only [physicalTerminalSegments, map_mul, mul_apply_eq_comp]
    rw [hd, map_smul, terminalSegments_last_probe e h hh heh]
  · have hl := (physical_terminal_search base hbase e h H0.gradient (m.direction H0) hh heh x y z n a t ht hg hd).1
    rw [hl, quadratic_gradient_eq_cg m hm _ (cgOperator_positive base hbase).1 (cgOperator_positive base hbase).2,
      hdir, map_smul, lineStep_smul _ _ _ hscale.ne']
    rfl
  · exact (physical_terminal_search base hbase e h H0.gradient (m.direction H0) hh heh x y z n a t ht hg hd).2

/-- The complete actual terminal data fibre holds under the article's original full energy-atom premise.
Use: no reference frame, terminal gradient, expansion or optimizer is assumed;
all true reference geometry is derived from the actual CG recurrence and actual spectral atoms.
Article: main_krylov, lem:terminal-fibre, common actual data and exact x√c residual.
Proof: the true energy-atom condition gives actual nonstagnation by the actual
residual-polynomial root bound; the proved true CG induction constructs the
actual orthonormal frame and full termination. Apply the proved actual protocol
fibre and identify its true reference step norm with √c. -/
theorem terminal_data_fibre (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hbase : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hN : 0<n)
    (hcount : referenceAtomCount base hbase g=n+1)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (n+1)))) (hm : CGConsistent m) (x : ℕ → ℝ) :
    let e := canonicalCGUnitStep base g 0
    let h := canonicalCGUnitStep base g n
    let a := Real.sqrt (cgEnergy base g n)
    let H0 := methodRun m (fun _ => cgOperator base) (fun _ => cgOperator base) g n
    ∃ t : ℝ, t≠0 ∧ ∀ (y z : ℕ → ℝ)
      (B : ℕ → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))),
      let H := methodRun m (fun k => Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ)
        (physicalTerminalSegments base e h x y z n k)) B g n
      let d := m.direction H
      let Z := Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) (physicalTerminalSegments base e h x y z n n) d
      H=H0 ∧
      Z=Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) (metricRoot base)
        (t • (h+(∑ l ∈ Finset.range n, x l) • e)) ∧
      lineLength H.gradient d Z • d=cgStep base g n ∧
      Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) (metricRoot base)⁻¹ (searchedGradient H.gradient d Z)=
        ((∑ l ∈ Finset.range n, x l)*a) • e := by
  simpa only [cgEnergy_sqrt base hbase] using terminal_data_fibre_of_frame base hbase g hN
    (canonicalCG_frame_of_full_atoms base hbase g hcount) m hm x

end
end krylov.Secant
