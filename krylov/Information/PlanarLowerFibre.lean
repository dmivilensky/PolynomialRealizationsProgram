import krylov.Information.PlanarAdmissibility
import krylov.Secant.TerminalFibre

/-!
Article: main_krylov, thm:C, actual admissible lower information fibres.
Use: connect the explicit all-budget signed physical family to the genuine
complete method history and its exact common last-probe residual.
Source: the actual full CG frame and the existing terminal-fibre execution
theorem; operator equalities identify precisely the constructed scenarios.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Secant krylov.Reference krylov.LinearAlgebra krylov.Correction
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator MatrixOrder
variable {n : ℕ}

/-- The explicit canonical lower scenario has exactly the actual terminal-fibre probe sequence.
Use: link proved individual budgets to the existing complete-history indistinguishability theorem.
Article: main_krylov, thm:C and lem:terminal-fibre, actual lower scenario probes.
Proof: the true initial hidden diagonal cancels the sum of all terminal
z-coefficients. Induction then uses the same exact planar increment at each
successor, preserving every actual probe operator.
-/
theorem planarLowerScenario_probe (e f : EuclideanSpace ℝ (Fin n)) (ω : ℕ → ℝ) (w : ℝ)
    (N : ℕ) (a γ σ : ℝ) (k : ℕ) :
    let t := 1-∑ i∈range N, ω i
    (planarLowerScenario e f ω w N a γ σ).probe k=
      terminalSegments e f (fun i => t*ω i*a) (fun i => t*ω i*(σ*γ))
        (fun i => t*ω i*(-(σ*γ))) N k := by
  -- The hidden initial base is fixed by the entire assigned finite profile.
  let W := ∑ i∈range N, ω i
  let t := 1-W
  have hz : (∑ i∈range N, t*ω i*(-(σ*γ)))= -(σ*t*γ*W) := by
    calc
      _ = (t*(-(σ*γ)))*W := by
        dsimp only [W]
        rw [mul_sum]
        exact sum_congr rfl fun i _ => by ring
      _ = _ := by ring
  induction k with
  | zero =>
    simp only [Scenario.probe,sum_range_zero,add_zero]
    change 1+planarMatrix f e (σ*t*γ*W) 0 0=
      terminalSegments e f (fun i => t*ω i*a) (fun i => t*ω i*(σ*γ))
        (fun i => t*ω i*(-(σ*γ))) N 0
    rw [terminalSegments_zero,hz]
    simp only [planarMatrix,zero_smul,add_zero,neg_smul]
    module
  | succ k ih =>
    rw [Scenario.probe_succ,ih]
    change terminalSegments e f _ _ _ N k+
      planarMatrix e f (t*ω k*(σ*γ)) (t*ω k*a) (t*ω k*(-(σ*γ)))=
        terminalSegments e f _ _ _ N (k+1)
    rw [← terminalSegments_increment e f (fun i => t*ω i*a) (fun i => t*ω i*(σ*γ))
      (fun i => t*ω i*(-(σ*γ))) N k]
    abel

/-- Inverse-root physical transport is the actual positive-root congruence for every matrix.
Use: prove the lower scenario oracle is precisely the physical terminal-fibre oracle.
Article: main_krylov, thm:C, exact physical operator transport.
Proof: symmetry and nonsingularity of the true positive root cancel both
inverse coordinate factors, retaining the arbitrary actual operator between them. -/
theorem inverseRootForm (A M : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    inverseFormMap (metricRoot A)⁻¹ M=metricRoot A*M*metricRoot A := by
  change ((metricRoot A)⁻¹)ᵀ⁻¹*M*((metricRoot A)⁻¹)⁻¹=_
  rw [transpose_nonsing_inv,Matrix.nonsing_inv_nonsing_inv _ (metricRoot_det_unit A hA)]
  rw [Matrix.nonsing_inv_nonsing_inv _ (by simpa only [det_transpose] using metricRoot_det_unit A hA)]
  rw [(metricRoot_isSymm A).eq]

/-- Every actual physical lower-scenario probe is the genuine physical terminal-fibre operator.
Use: the constructed admissible family inherits complete nonanticipating observation equality.
Article: main_krylov, thm:C and lem:terminal-fibre, physical lower scenario oracle.
Proof: linear transport commutes with the actual probe sum; the proved
canonical sequence and genuine inverse-root congruence give the physical operator. -/
theorem physical_planarLowerScenario_probe (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (e f : EuclideanSpace ℝ (Fin n)) (ω : ℕ → ℝ) (w : ℝ)
    (N : ℕ) (a γ σ : ℝ) (k : ℕ) :
    let t := 1-∑ i∈range N, ω i
    ((planarLowerScenario e f ω w N a γ σ).inPhysical (metricRoot A)⁻¹).probe k=
      physicalTerminalSegments A e f (fun i => t*ω i*a) (fun i => t*ω i*(σ*γ))
        (fun i => t*ω i*(-(σ*γ))) N k := by
  change (Scenario.mapForms _ (inverseFormMap (metricRoot A)⁻¹)).probe k=_
  rw [Scenario.mapForms_probe,planarLowerScenario_probe,inverseRootForm A _ hA]
  rfl

/-- The actual full spectral reference derives every geometric premise of the admissible signed lower family.
Use: all-profile physical lower scenarios require only the original genuine n-atom reference data.
Article: main_krylov, thm:C, admissible lower scenarios on the actual CG frame.
Proof: the original full active-atom condition supplies the true orthonormal
CG frame. Its genuine first and last unit steps discharge the real unit and
orthogonality conditions in the proved physical all-budget construction.
-/
theorem cg_planarLowerScenario_admissible {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1)
    (ω : ℕ → ℝ) (w τ r : ℝ)
    (hω : ∀ i∈range N, 0≤ω i) (hw : 0≤w) (hτ : 0≤τ)
    (hW : (∑ i∈range N, ω i)<1) (hWr : (∑ i∈range N, ω i)≤r)
    (a γ σ : ℝ) (hγ : 0≤γ) (hac : a^2+γ^2=1) (hσ : σ^2=1) :
    ((planarLowerScenario (canonicalCGUnitStep A g 0) (canonicalCGUnitStep A g N)
      ω w N a γ σ).inPhysical (metricRoot A)⁻¹).Admissible N A r ω w τ := by
  -- Every actual witness direction belongs to the genuine full reference frame.
  have ho := canonicalCG_frame_of_full_atoms A hA g hcount
  have he : ‖canonicalCGUnitStep A g 0‖=1 := by
    simpa only [Fin.val_zero] using ho.norm_eq_one (0 : Fin (N+1))
  have hf : ‖canonicalCGUnitStep A g N‖=1 := by
    simpa only [Fin.val_last] using ho.norm_eq_one (Fin.last N)
  have hef : inner ℝ (canonicalCGUnitStep A g 0) (canonicalCGUnitStep A g N)=0 := by
    simpa only [Fin.val_zero,Fin.val_last] using
      (ho.inner_eq_zero (i := 0) (j := Fin.last N) (by
        intro h
        have hv : (0 : ℕ)=N := congrArg Fin.val h
        omega))
  exact physical_planarLowerScenario_admissible A hA _ _ he hf hef ω w τ r N
    hω hw hτ hW hWr a γ σ hγ hac hσ

/-- The explicit physical lower family has identical complete actual preterminal data for every globally CG-consistent method.
Use: the proved admissible signed scenarios are indistinguishable before the common actual final correction decision.
Article: main_krylov, thm:C and lem:terminal-fibre, actual all-profile information fibre.
Proof: the exact physical probe identity places the constructed operators
in the existing genuine terminal fibre. Full active spectral data derive
all true CG geometry. Its complete history, last probe, reference line step
and exact incoming residual depend only on the common cross sum t a W₀.
-/
theorem physical_planarLowerScenario_data_fibre {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1)
    (m : krylov.Methods.ProbedMethod (EuclideanSpace ℝ (Fin (N+1))))
    (hm : krylov.Methods.CGConsistent m) (ω : ℕ → ℝ) (w a γ : ℝ) :
    let e := canonicalCGUnitStep A g 0
    let f := canonicalCGUnitStep A g N
    let W := ∑ i∈range N, ω i
    let t := 1-W
    let H₀ := krylov.Methods.methodRun m (fun _ => cgOperator A) (fun _ => cgOperator A) g N
    ∃ c : ℝ, c≠0 ∧ ∀ (σ : ℝ)
      (B : ℕ → EuclideanSpace ℝ (Fin (N+1)) →L[ℝ] EuclideanSpace ℝ (Fin (N+1))),
      let S := (planarLowerScenario e f ω w N a γ σ).inPhysical (metricRoot A)⁻¹
      let Q := fun i => cgOperator (S.probe i)
      let H := krylov.Methods.methodRun m Q B g N
      let d := m.direction H
      let z := Q N d
      H=H₀ ∧ z=cgOperator (metricRoot A) (c • (f+(t*a*W) • e)) ∧
        lineLength H.gradient d z • d=cgStep A g N ∧
        cgOperator (metricRoot A)⁻¹ (searchedGradient H.gradient d z)=
          (t*a*W*Real.sqrt (cgEnergy A g N)) • e := by
  -- Apply the genuine complete-history theorem only after identifying the actual physical probes.
  let W := ∑ i∈range N, ω i
  let t := 1-W
  let e := canonicalCGUnitStep A g 0
  let f := canonicalCGUnitStep A g N
  obtain ⟨c,hc,hd⟩ := terminal_data_fibre A hA g hN hcount m hm (fun i => t*ω i*a)
  refine ⟨c,hc,?_⟩
  intro σ B
  have hp := hd (fun i => t*ω i*(σ*γ)) (fun i => t*ω i*(-(σ*γ))) B
  have hprobe : (fun i => cgOperator
      (((planarLowerScenario e f ω w N a γ σ).inPhysical (metricRoot A)⁻¹).probe i))=
        (fun i => cgOperator (physicalTerminalSegments A e f (fun i => t*ω i*a)
          (fun i => t*ω i*(σ*γ)) (fun i => t*ω i*(-(σ*γ))) N i)) := by
    funext i
    exact congrArg cgOperator (physical_planarLowerScenario_probe A hA e f ω w N a γ σ i)
  have hsum : (∑ i∈range N, t*ω i*a)=t*a*W := by
    dsimp only [W]
    rw [mul_sum]
    exact sum_congr rfl fun i _ => by ring
  dsimp only at hp ⊢
  rw [hprobe]
  simp only [physical_planarLowerScenario_probe A hA]
  simpa only [hsum,e,f,t,W,cgOperator] using hp

end
end krylov.Information
