import krylov.Secant.TerminalRadius
import krylov.Reference.CanonicalSteps
import krylov.Methods.QuadraticConsistency

/-!
Article: main_krylov, lem:terminal-fibre, actual physical prefix indistinguishability.
Use: derive equality of full histories for every genuine nonanticipating
CG-consistent policy, using the actual normalized steps of the concrete CG run.
Source: actual root congruence, reference step orthogonality and the proved protocol induction.
-/

namespace krylov.Secant
noncomputable section
open Matrix krylov.LinearAlgebra krylov.Reference krylov.Methods
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
variable {n : ℕ}

/-- The actual physical planar segment matrix, obtained by the genuine positive-root congruence.
Use: the information construction lives in the article's actual physical operator model.
Article: main_krylov, lem:terminal-fibre, A_k=A^(1/2)Â_kA^(1/2). -/
def physicalTerminalSegments (base : Matrix (Fin n) (Fin n) ℝ)
    (e h : EuclideanSpace ℝ (Fin n)) (x y z : ℕ → ℝ) (N k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  metricRoot base*terminalSegments e h x y z N k*metricRoot base

/-- Every actual physical planar segment has exactly its prescribed canonical matrix.
Use: physical positivity/budgets and the actual normalized probe use the same genuine coordinates.
Article: main_krylov, lem:terminal-fibre, physical/canonical construction.
Proof: cancel both actual positive roots against their actual inverses. -/
theorem physicalTerminal_relative (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (e h : EuclideanSpace ℝ (Fin n)) (x y z : ℕ → ℝ) (N k : ℕ) :
    relativeOperator base (physicalTerminalSegments base e h x y z N k)=terminalSegments e h x y z N k := by
  have hR := metricRoot_det_unit base hbase
  simp only [relativeOperator, physicalTerminalSegments, ← Matrix.mul_assoc]
  rw [nonsing_inv_mul _ hR, Matrix.one_mul, Matrix.mul_assoc, mul_nonsing_inv _ hR, Matrix.mul_one]

/-- A canonical reference probe fixed by the planar segment gives the actual unchanged physical probe.
Use: connects the exact planar action to the actual query direction used by the policy.
Article: main_krylov, lem:terminal-fibre, invisible physical prefix probes.
Proof: the true physical segment acts by root, planar action, root; the
reference acts by two actual roots, which square to its real physical base. -/
theorem physicalTerminal_probe_eq (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (e h d : EuclideanSpace ℝ (Fin n)) (x y z : ℕ → ℝ) (N k : ℕ)
    (hp : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (terminalSegments e h x y z N k)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base) d)=
        Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (metricRoot base) d) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (physicalTerminalSegments base e h x y z N k) d=cgOperator base d := by
  simp only [physicalTerminalSegments, map_mul, mul_apply_eq_comp]
  rw [hp, ← mul_apply_eq_comp, ← map_mul, metricRoot_square base hbase]
  rfl

/-- Genuine orthonormal reference steps force every actual planar preterminal CG probe to be unchanged.
Use: discharges matching-probe assumptions from actual reference step geometry, not assumed histories.
Article: main_krylov, lem:terminal-fibre, first and middle reference directions.
Proof: the actual first canonical step lies along e; every actual middle step
is orthogonal to both e and h. Actual nonzero line scaling transfers these
fixed planar actions to the genuine CG query directions. -/
theorem terminal_reference_prefix_probes (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 0<N)
    (ho : Orthonormal ℝ (fun i : Fin (N+1) => canonicalCGUnitStep base g i.val))
    (x y z : ℕ → ℝ) :
    let e := canonicalCGUnitStep base g 0
    let h := canonicalCGUnitStep base g N
    ∀ k<N, Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (physicalTerminalSegments base e h x y z N k) (cgRun (cgOperator base) g k).direction=
        cgOperator base (cgRun (cgOperator base) g k).direction := by
  -- Prove the fixed planar action on normalized actual steps before rescaling the actual query direction.
  dsimp only
  let e := canonicalCGUnitStep base g 0
  let h := canonicalCGUnitStep base g N
  have heh : inner ℝ e h=0 := ho.inner_eq_zero (i := 0) (j := Fin.last N)
    (show (0 : Fin (N+1))≠Fin.last N by
    intro hz
    have hv := congrArg Fin.val hz
    simp only [Fin.val_zero, Fin.val_last] at hv
    omega)
  intro k hk
  let i : Fin (N+1) := ⟨k, hk.trans_le (Nat.le_succ N)⟩
  have hs : canonicalCGStep base g k≠0 := by
    intro hz
    have hn := ho.norm_eq_one i
    change ‖canonicalCGUnitStep base g k‖=1 at hn
    simp only [canonicalCGUnitStep, hz, NormedSpace.normalize_zero_eq_zero, norm_zero] at hn
    exact zero_ne_one hn
  have hfixed : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (terminalSegments e h x y z N k)
      (canonicalCGUnitStep base g k)=canonicalCGUnitStep base g k := by
    by_cases hk0 : k=0
    · subst k
      exact terminalSegments_first_probe e h heh x y z N
    · apply terminalSegments_middle_probe
      · exact ho.inner_eq_zero (i := 0) (j := i)
          (show (0 : Fin (N+1))≠i by intro hz; exact hk0 (congrArg Fin.val hz).symm)
      · exact ho.inner_eq_zero (i := Fin.last N) (j := i)
          (show Fin.last N≠i by intro hz; have hv := congrArg Fin.val hz; dsimp [i] at hv; omega)
  apply physicalTerminal_probe_eq base hbase e h _ x y z N k
  have hdir := canonicalCG_direction base g k hs
  have hn : canonicalCGStep base g k=‖canonicalCGStep base g k‖ • canonicalCGUnitStep base g k :=
    (NormedSpace.norm_smul_normalize (canonicalCGStep base g k)).symm
  rw [hn] at hdir
  rw [hdir]
  simp only [map_smul, canonicalCGUnitStep] at hfixed ⊢
  rw [hfixed]

/-- Every actual nonanticipating globally CG-consistent policy has exactly the full reference prefix history.
Use: finite adaptive correction traces, gradients, steps and all prior probes are genuinely indistinguishable.
Article: main_krylov, lem:terminal-fibre, all data through iteration n−2.
Proof: the actual reference geometry gives every true matching CG probe;
the proved positive reference operator and full nonanticipating shadow induction then apply. -/
theorem terminal_method_prefix (base : Matrix (Fin n) (Fin n) ℝ) (hbase : base.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (hN : 0<N)
    (ho : Orthonormal ℝ (fun i : Fin (N+1) => canonicalCGUnitStep base g i.val))
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n))) (hm : CGConsistent m)
    (x y z : ℕ → ℝ) (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    ∀ k≤N,
      methodRun m (fun j => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
        (physicalTerminalSegments base (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g N) x y z N j)) B g k=
          methodRun m (fun _ => cgOperator base) (fun _ => cgOperator base) g k := by
  exact cgConsistent_shadow m hm (cgOperator base) (cgOperator_positive base hbase).1
    (cgOperator_positive base hbase).2 _ B g N
    (terminal_reference_prefix_probes base hbase g N hN ho x y z)

end
end krylov.Secant
