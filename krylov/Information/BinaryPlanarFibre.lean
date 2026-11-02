import krylov.Information.BinaryPlanarModel

/-!
Article: main_krylov, thm:H, the actual gradient-only binary information fibre.
Use: prove identical complete preterminal histories and last probes for the
two compatible signed tensors, then derive their actual common one-query
terminal correction. Source: genuine terminal CG shadow, nonanticipation,
and exact physical positive-root transport. No output formula is assumed.
-/

namespace krylov.Information
noncomputable section
open Real Matrix Finset krylov.Tensor krylov.Tensor.BinaryCubic krylov.Secant
  krylov.Reference krylov.LinearAlgebra krylov.Correction krylov.Methods
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ}

/-- Every globally CG-consistent at-most-one-correction method has a common actual terminal query on the two genuine compatible binary scenarios.
Article: main_krylov, thm:H, the original information-class lower-bound domain.
All histories, probes and post-search gradients are actual executions of the
operator policy. The common-query normal form follows from nonanticipation. -/
theorem binaryPlanarWitness_terminal_form
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0 < N)
    (hcount : referenceAtomCount A hA g = N+1)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (hm : CGConsistent m)
    (h1 : OneCorrectionMethod m) (κ r : ℝ) :
    let e := canonicalCGUnitStep A g 0
    let h := canonicalCGUnitStep A g N
    let ψ := κ / (sqrt 2 * (1+r))
    let a := sqrt (cgEnergy A g N)
    let M := 1 + planarMatrix e h (2*r*ψ) ψ (-r*ψ)
    let Δ := planarMatrix e h ((1+2*r^2)*ψ) (-r*ψ) 0
    let probes := fun σ => binaryPlanarProbe A e h κ r N (gradientWitness r σ)
    let corrections := fun σ (_ : ℕ) => cgOperator
      (metricRoot A * binaryPlanarOutput e h κ r N (gradientWitness r σ) * metricRoot A)
    ∃ u : EuclideanSpace ℝ (Fin (N+1)), ∀ σ : ℝ,
      cgOperator (metricRoot A)⁻¹ (probedGradient m (probes σ) (corrections σ) g (N+1)) =
        (ψ*a) • e + cgOperator (M + σ • Δ) u := by
  let e := canonicalCGUnitStep A g 0
  let h := canonicalCGUnitStep A g N
  let ψ := κ / (sqrt 2 * (1+r))
  let a := sqrt (cgEnergy A g N)
  let H₀ := methodRun m (fun _ => cgOperator A) (fun _ => cgOperator A) g N
  let probe := fun σ => binaryPlanarProbe A e h κ r N (gradientWitness r σ)
  let output := fun σ => binaryPlanarOutput e h κ r N (gradientWitness r σ)
  let corr := fun σ (_ : ℕ) => cgOperator (metricRoot A * output σ * metricRoot A)
  have ho := canonicalCG_frame_of_full_atoms A hA g hcount
  have hh : ‖h‖ = 1 := ho.norm_eq_one (Fin.last N)
  have heh : inner ℝ e h = 0 := ho.inner_eq_zero (i := 0) (j := Fin.last N)
    (by intro hz; have hv := congrArg Fin.val hz; simp only [Fin.val_zero, Fin.val_last] at hv; omega)
  have hs : canonicalCGStep A g N ≠ 0 := by
    intro hz
    exact ho.ne_zero (Fin.last N) (by simp only [canonicalCGUnitStep, Fin.val_last, hz,
      NormedSpace.normalize_zero_eq_zero])
  obtain ⟨scale, _, hdir, _⟩ := hm (cgOperator A) (cgOperator_positive A hA).1 (cgOperator_positive A hA).2 g N
  let t := scale * (cgLine A g N)⁻¹ * a
  have hstep : canonicalCGStep A g N = a • h := by
    change canonicalCGStep A g N = sqrt (cgEnergy A g N) • h
    rw [cgEnergy_sqrt A hA]
    exact (NormedSpace.norm_smul_normalize _).symm
  have hd : cgOperator (metricRoot A) (m.direction H₀) = t • h := by
    rw [hdir, map_smul]
    change scale • Matrix.toEuclideanCLM (n := Fin (N+1)) (𝕜 := ℝ) (metricRoot A)
      (cgRun (cgOperator A) g N).direction = t • h
    rw [canonicalCG_direction A g N hs, hstep, smul_smul, smul_smul]
  let z₀ := cgOperator (metricRoot A) (t • (h + ψ • e))
  have hp (σ : ℝ) : methodRun m (probe σ) (corr σ) g N = H₀ := by
    simpa only [probe, binaryPlanarProbe, binaryPlanarSegments, physicalTerminalSegments, cgOperator, e, h, H₀] using!
      terminal_method_prefix A hA g N hN ho m hm
        (binaryFirstLast N (κ*(gradientWitness r σ).t1) (κ*r*(gradientWitness r σ).t2))
        (binaryFirstLast N (κ*(gradientWitness r σ).t0) (κ*r*(gradientWitness r σ).t1))
        (binaryFirstLast N (κ*(gradientWitness r σ).t2) (κ*r*(gradientWitness r σ).t3))
        (corr σ) N le_rfl
  have hz (σ : ℝ) : probe σ N (m.direction H₀) = z₀ := by
    dsimp only [probe, binaryPlanarProbe, z₀]
    simp only [cgOperator, map_mul, mul_apply_eq_comp]
    change cgOperator (metricRoot A)
      (cgOperator (binaryPlanarSegments e h κ r N (gradientWitness r σ) N)
        (cgOperator (metricRoot A) (m.direction H₀))) = _
    rw [hd, map_smul]
    rw [binaryPlanarSegments_last_probe e h hh heh κ r N hN, gradientWitness_cross]
    rw [show κ * (1 / (sqrt 2 * (1+r))) = ψ by dsimp only [ψ]; ring]
    rfl
  have hpost : cgOperator (metricRoot A)⁻¹
      (searchedGradient H₀.gradient (m.direction H₀) z₀) = (ψ*a) • e := by
    let w := gradientWitness r 1
    obtain ⟨c, _, hdata⟩ := terminal_data_fibre A hA g hN hcount m hm
      (binaryFirstLast N (κ*w.t1) (κ*r*w.t2))
    have hh := hdata (binaryFirstLast N (κ*w.t0) (κ*r*w.t1))
      (binaryFirstLast N (κ*w.t2) (κ*r*w.t3)) (corr 1)
    have hp' : methodRun m (probe 1) (corr 1) g N = H₀ := hp 1
    have hh' : cgOperator (metricRoot A)⁻¹
        (searchedGradient (methodRun m (probe 1) (corr 1) g N).gradient
          (m.direction (methodRun m (probe 1) (corr 1) g N))
          (probe 1 N (m.direction (methodRun m (probe 1) (corr 1) g N)))) =
        ((∑ j ∈ range N, binaryFirstLast N (κ*w.t1) (κ*r*w.t2) j)*a) • e := hh.2.2.2
    rw [hp', hz 1, binaryFirstLast_sum N hN] at hh'
    have heq : κ*w.t1 + κ*r*w.t2 = ψ := by
      calc
        _ = κ*(w.t1+r*w.t2) := by ring
        _ = ψ := by rw [show w=gradientWitness r 1 from rfl, gradientWitness_cross]; dsimp only [ψ]; ring
    rw [heq] at hh'
    exact hh'
  let u₀ := firstCorrectionStep (m.correction H₀ z₀)
  refine ⟨cgOperator (metricRoot A) u₀, ?_⟩
  intro σ
  have hgout : probedGradient m (probe σ) (corr σ) g (N+1) =
      searchedGradient H₀.gradient (m.direction H₀) z₀ + corr σ N u₀ := by
    rw [probedGradient_succ]
    change (runCorrections _ _ _).gradient = _
    rw [one_correction_gradient _ (h1 _ _), hp σ, hz σ]
  change cgOperator (metricRoot A)⁻¹ (probedGradient m (probe σ) (corr σ) g (N+1)) = _
  rw [hgout, map_add, hpost]
  congr 1
  change cgOperator (metricRoot A)⁻¹
    (cgOperator (metricRoot A * output σ * metricRoot A) u₀) = _
  rw [← inverseRootForm A (output σ) hA, inverseRootForm_action A (output σ) hA]
  dsimp only [output]
  rw [binaryPlanarOutput_witness e h κ r σ N hN]

end
end krylov.Information
