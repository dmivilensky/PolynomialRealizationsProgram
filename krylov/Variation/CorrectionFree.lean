import krylov.Methods.FC
import krylov.Secant.TerminalFibre
import krylov.LinearAlgebra.PlanarAggregation

/-!
Article: main_krylov, s3:cor:cf, actual correction-free obstruction.
Use: specialize the actual terminal data fibre to correction-free policies,
including real FC, and verify positive physical operators with assigned budgets.
Source: the already proved actual terminal fibre and its genuine planar matrices.
-/

namespace krylov.Variation
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.LinearAlgebra
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A probed policy whose actual correction rule always finishes without another query.
Use: the exact obstruction quantifies over all data-dependent correction-free consistent policies.
Article: main_krylov, s3:cor:cf, no corrections. -/
def CorrectionFree (m : ProbedMethod E) : Prop := ∀ H z, m.correction H z=.done

/-- Every actual FC policy is correction-free for every observed history.
Use: specialize the universal exact obstruction to full or windowed FC.
Article: main_krylov, alg:fc and s3:cor:cf.
Proof: FC's actual correction decision tree is empty by definition. -/
theorem fcMethod_correctionFree (memory : ℕ → ℕ) : CorrectionFree (fcMethod memory : ProbedMethod E) :=
  fun _ _ => rfl

variable {n : ℕ}

/-- The actual correction-free terminal residual has exactly the prescribed total cross budget times the true last-step energy root.
Use: the universal information obstruction is realized by actual executed policies, including their full observed prefix.
Article: main_krylov, s3:cor:cf, exact W₀√c_(n−1) residual.
Proof: the actual terminal data fibre fixes the true last probe and actual
post-search residual; the empty final correction tree makes that residual the actual returned gradient. -/
theorem correctionFree_terminal_residual
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hn : 0<n) (hcount : referenceAtomCount base hb g=n+1)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (n+1)))) (hm : CGConsistent m) (hfree : CorrectionFree m)
    (ω : ℕ → ℝ) (hω : ∀ l<n, 0≤ω l)
    (B : ℕ → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))) :
    let e := canonicalCGUnitStep base g 0
    let h := canonicalCGUnitStep base g n
    let A := fun k => Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ)
      (physicalTerminalSegments base e h ω 0 0 n k)
    ‖Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) (metricRoot base)⁻¹
      (methodRun m A B g (n+1)).gradient‖=(∑ l∈range n, ω l)*Real.sqrt (cgEnergy base g n) := by
  -- The same actual last search is forced for every correction-free policy by the full observed-prefix fibre.
  obtain ⟨_,_,hf⟩ := terminal_data_fibre base hb g hn hcount m hm ω
  have he := (hf 0 0 B).2.2.2
  dsimp only at he ⊢
  change ‖Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) (metricRoot base)⁻¹
    (runCorrections (m.correction _ _) _ _).gradient‖=_
  rw [hfree]
  change ‖Matrix.toEuclideanCLM (n := Fin (n+1)) (𝕜 := ℝ) (metricRoot base)⁻¹ (searchedGradient _ _ _)‖=_
  have he0 : ‖canonicalCGUnitStep base g 0‖=1 := by
    simpa only [Fin.val_zero] using (canonicalCG_frame_of_full_atoms base hb g hcount).norm_eq_one (0 : Fin (n+1))
  rw [he, norm_smul, Real.norm_eq_abs,
    he0, mul_one]
  exact congrArg (fun t => t) (abs_of_nonneg (mul_nonneg
    (sum_nonneg fun l hl => hω l (mem_range.mp hl)) (Real.sqrt_nonneg _)))

/-- The actual correction-free planar segment operators are positive throughout every subunit total-budget cycle.
Use: the exact obstruction uses admissible positive physical quadratics, not formal indefinite perturbations.
Article: main_krylov, s3:cor:cf, W₀<1.
Proof: each nonnegative partial cross budget is at most the subunit total;
the proved canonical planar positivity transfers through the genuine invertible positive metric root. -/
theorem correctionFree_segments_posDef
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hn : 0<n) (hcount : referenceAtomCount base hb g=n+1)
    (ω : ℕ → ℝ) (hω : ∀ l<n, 0≤ω l) (hW : ∑ l∈range n, ω l<1)
    {k : ℕ} (hk : k≤n) :
    (physicalTerminalSegments base (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g n) ω 0 0 n k).PosDef := by
  -- All canonical prefix models use the same actual orthonormal first/last CG plane.
  have ho := canonicalCG_frame_of_full_atoms base hb g hcount
  have heh : inner ℝ (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g n)=0 :=
    ho.inner_eq_zero (i := 0) (j := Fin.last n) (by
      intro he
      have h := congrArg Fin.val he
      simp only [Fin.val_zero, Fin.val_last] at h
      omega)
  have hp : 0≤∑ l∈range k, ω l := sum_nonneg fun l hl => hω l ((mem_range.mp hl).trans_le hk)
  have hle : (∑ l∈range k, ω l)≤∑ l∈range n, ω l :=
    sum_le_sum_of_subset_of_nonneg (range_mono hk) (fun l hl _ => hω l (mem_range.mp hl))
  have hc := terminal_cross_posDef _ _ (ho.norm_eq_one 0) (ho.norm_eq_one (Fin.last n)) heh
    (by rw [abs_of_nonneg hp]; exact hle.trans_lt hW)
  have hcan : (terminalSegments (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g n) ω 0 0 n k).PosDef := by
    simpa only [terminalSegments, Pi.zero_apply, sum_const_zero, sub_zero, Fin.val_zero, Fin.val_last] using hc
  have hinj : Function.Injective (metricRoot base).mulVec := by
    intro v w he
    have h := congrArg (fun u => (metricRoot base)⁻¹ *ᵥ u) he
    simpa only [mulVec_mulVec, nonsing_inv_mul _ (metricRoot_det_unit base hb), one_mulVec] using h
  simpa only [physicalTerminalSegments, conjTranspose_eq_transpose_of_trivial, (metricRoot_isSymm base).eq, ← Matrix.mul_assoc]
    using hcan.conjTranspose_mul_mul_same (B := metricRoot base) hinj

/-- Each actual physical correction-free obstruction increment obeys its prescribed canonical spectral budget.
Use: the exact residual family has the source's independent secant increment budgets.
Article: main_krylov, s3:cor:cf, E_l=ω_l(q₀q_lastᵀ+q_lastq₀ᵀ).
Proof: genuine inverse-root congruence gives the exact planar increment;
the already proved actual planar spectral contraction gives its assigned norm. -/
theorem correctionFree_increment_budget
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hn : 0<n) (hcount : referenceAtomCount base hb g=n+1)
    (ω : ℕ → ℝ) (hω : ∀ l<n, 0≤ω l) {k : ℕ} (hk : k<n) :
    relativeBudget base
      (physicalTerminalSegments base (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g n) ω 0 0 n (k+1)-
        physicalTerminalSegments base (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g n) ω 0 0 n k)≤ω k := by
  -- The actual physical difference is transformed by the very same genuine reference metric.
  have ho := canonicalCG_frame_of_full_atoms base hb g hcount
  have heh : inner ℝ (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g n)=0 :=
    ho.inner_eq_zero (i := 0) (j := Fin.last n) (by
      intro he
      have h := congrArg Fin.val he
      simp only [Fin.val_zero, Fin.val_last] at h
      omega)
  have hr : ∀ X Y : Matrix (Fin (n+1)) (Fin (n+1)) ℝ,
      relativeOperator base (X-Y)=relativeOperator base X-relativeOperator base Y := by
    intros
    simp only [relativeOperator, Matrix.mul_sub, Matrix.sub_mul]
  unfold relativeBudget
  rw [hr, physicalTerminal_relative _ hb, physicalTerminal_relative _ hb, terminalSegments_increment]
  change chebyshev1.opNorm (planarMatrix _ _ 0 (ω k) 0)≤ω k
  have hs := planar_spectral_norm_le _ _ (ho.norm_eq_one 0) (ho.norm_eq_one (Fin.last n)) heh 0 1 (by norm_num)
  have hc : planarMatrix (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g n) 0 (ω k) 0=
      ω k • planarMatrix (canonicalCGUnitStep base g 0) (canonicalCGUnitStep base g n) 0 1 0 := by
    simpa only [mul_zero, mul_one] using planarMatrix_scale _ _ (ω k) 0 1 0
  rw [hc, chebyshev1.opNorm_smul, abs_of_nonneg (hω k hk)]
  simpa only [neg_zero, mul_one, Fin.val_zero, Fin.val_last] using mul_le_mul_of_nonneg_left hs (hω k hk)

end
end krylov.Variation
