import jacobi.Continuum.Cycles
import Mathlib.MeasureTheory.Integral.Pi

/-!
Article: jacobi, Appendix D.1 (strict concentration gain).
The nested cycle formula is identified with the ordinary Lebesgue integral on
R^p. Absolute integrability is proved from the product of the density norms,
so all changes between product and iterated integrals use genuine Fubini theorems.
Source: mathlib, finite product measures and the Bochner Fubini theorem.
Use: product-space version of chainKernel, with both endpoints retained.
-/
namespace jacobi.Continuum
noncomputable section
open MeasureTheory Real
open scoped BigOperators

/-- An open exponential path with n integrated interior vertices.
Use: product-space version of chainKernel, with both endpoints retained.
Article: jacobi, Appendix D.1 (strict concentration gain).
-/
def pathIntegrand (m : ℝ → ℝ) : (n : ℕ) → ℝ → ℝ → (Fin n → ℝ) → ℝ
  | 0, x, y, _ => exp (-|x-y|)
  | n+1, x, y, z => m (z 0) * exp (-|x-z 0|) * pathIntegrand m n (z 0) y (Fin.tail z)

/-- Exponential path integrands are measurable in any measurable parameters.
Use: proves strong measurability before domination and Fubini.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: each recursion step multiplies a measurable density, a continuous kernel,
and the preceding measurable path. -/
theorem pathIntegrand_measurable {D : Type*} [MeasurableSpace D] {m : ℝ → ℝ}
    (hm : Measurable m) (n : ℕ) {x y : D → ℝ} {z : D → Fin n → ℝ}
    (hx : Measurable x) (hy : Measurable y) (hz : ∀ i, Measurable (fun a => z a i)) :
    Measurable (fun a => pathIntegrand m n (x a) (y a) (z a)) := by
  induction n generalizing x y with
  | zero => exact measurable_exp.comp ((continuous_abs.measurable.comp (hx.sub hy)).neg)
  | succ n ih =>
    exact ((hm.comp (hz 0)).mul (measurable_exp.comp ((continuous_abs.measurable.comp (hx.sub (hz 0))).neg))).mul
      (ih (hz 0) hy (fun i => hz i.succ))

/-- The absolute path integrand is dominated by independent density norms.
Use: the product majorant is integrable on the full finite product space.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: every exponential link is at most one; induction removes them successively. -/
theorem pathIntegrand_bound (m : ℝ → ℝ) (n : ℕ) (x y : ℝ) (z : Fin n → ℝ) :
    |pathIntegrand m n x y z| ≤ ∏ i, |m (z i)| := by
  -- Remove one exponential link at a time, keeping the product density majorant.
  induction n generalizing x y with
  | zero =>
    simp only [pathIntegrand, abs_of_pos (exp_pos _), Finset.univ_eq_empty, Finset.prod_empty]
    exact exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg (x-y)))
  | succ n ih =>
    rw [pathIntegrand, abs_mul, abs_mul, abs_of_pos (exp_pos _), Fin.prod_univ_succ]
    calc
      _ ≤ (|m (z 0)| * exp (-|x-z 0|)) * ∏ i : Fin n, |m (z i.succ)| :=
        mul_le_mul_of_nonneg_left (ih (z 0) y (Fin.tail z)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right (abs_nonneg _) (exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))))
        (Finset.prod_nonneg (fun i _ => abs_nonneg _))

/-- Open path integrands are absolutely integrable in all their interior vertices.
Use: every product-to-iterated conversion below is licensed by absolute integrability.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: dominate by the product of the integrable one-variable functions |m|. -/
theorem pathIntegrand_integrable {m : ℝ → ℝ} (hm : Integrable m) (hmm : Measurable m)
    (n : ℕ) (x y : ℝ) : Integrable (pathIntegrand m n x y) := by
  have h : Integrable (fun z : Fin n → ℝ => ∏ i, |m (z i)|) :=
    Integrable.fintype_prod (fun _ => hm.abs)
  apply h.mono'
  · exact (pathIntegrand_measurable hmm n measurable_const measurable_const
      (fun i => measurable_pi_apply i)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using pathIntegrand_bound m n x y z

/-- Splitting off the first coordinate of a finite product integral.
Use: converts the explicit path and cycle integrals into the nested kernel formula.
Article: jacobi, Appendix D.1 (strict concentration gain).
Source: mathlib, the measure-preserving finite-coordinate equivalence and Fubini.
Proof: separate coordinate zero with piFinSuccAbove, then integrate the product space. -/
theorem integral_fin_cons {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ) (hf : Integrable f) :
    (∫ z, f z) = ∫ x : ℝ, ∫ y : Fin n → ℝ, f (Fin.cons x y) := by
  -- The finite-coordinate equivalence preserves volume, so absolute integrability transfers to the product.
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have hi : Integrable (fun z : ℝ × (Fin n → ℝ) => f (e z)) :=
    (he.integrable_comp hf.aestronglyMeasurable).mpr hf
  have h : (∫ z : ℝ × (Fin n → ℝ), f (e z) ∂volume.prod volume) = ∫ z, f z :=
    he.integral_comp' f
  rw [integral_prod _ hi] at h
  simpa only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq] using h.symm

/-- The ordinary multiple path integral equals the proved nested chain kernel.
Use: closes the product-space cycle into its spectral moment.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: Fubini separates the first interior vertex; induction identifies the
remaining integral and fixed scalar factors commute with integration. -/
theorem path_integral {m : ℝ → ℝ} (hm : Integrable m) (hmm : Measurable m)
    (n : ℕ) (x y : ℝ) : (∫ z : Fin n → ℝ, pathIntegrand m n x y z) = chainKernel m n x y := by
  -- Fubini separates the first interior vertex; the induction hypothesis handles all remaining vertices.
  induction n generalizing x y with
  | zero =>
    simp only [pathIntegrand, chainKernel, integral_const]
    rw [Measure.volume_pi_eq_dirac]
    simp
  | succ n ih =>
    rw [integral_fin_cons _ (pathIntegrand_integrable hm hmm _ x y), chainKernel]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t => by
      simp only [pathIntegrand, Fin.cons_zero, Fin.tail_cons, integral_const_mul]
      rw [ih]
      ring

/-- The explicit product of all density factors and all links of an open path.
Use: identifies the recursive integrand with the literal multiple-integral formula.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: split off the first vertex and the first adjacent link, then use induction. -/
theorem pathIntegrand_product (m : ℝ → ℝ) (n : ℕ) (x y : ℝ) (z : Fin (n+1) → ℝ) :
    pathIntegrand m (n+1) x y z =
      (∏ i, m (z i)) * exp (-|x-z 0|) *
      (∏ i : Fin n, exp (-|z i.castSucc-z i.succ|)) * exp (-|z (Fin.last n)-y|) := by
  -- Splitting the finite products separates the first density and the first link.
  induction n generalizing x y with
  | zero => simp [pathIntegrand]
  | succ n ih =>
    rw [pathIntegrand, ih]
    simp only [Fin.prod_univ_succ, Fin.tail, Fin.succ_castSucc, Fin.succ_last, Fin.castSucc_zero]
    ring

/-- The closed cycle on n+1 physical vertices, before integrating any coordinate.
Use: its Lebesgue integral on R^(n+1) is the spectral moment.
Article: jacobi, Appendix D.1 (strict concentration gain).
-/
def cycleIntegrand (m : ℝ → ℝ) (n : ℕ) (z : Fin (n+1) → ℝ) : ℝ :=
  m (z 0) * pathIntegrand m n (z 0) (z 0) (Fin.tail z)

/-- The cycle integrand is precisely the printed product of densities and kernel links.
Use: connects the product-space theorem below to the article's literal formula.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: expand the open path; its first link joins vertices zero and one, and
its last link closes the last vertex to vertex zero. -/
theorem cycleIntegrand_product (m : ℝ → ℝ) (n : ℕ) (z : Fin (n+1) → ℝ) :
    cycleIntegrand m n z = (∏ i, m (z i)) *
      (∏ i : Fin n, exp (-|z i.castSucc-z i.succ|)) * exp (-|z (Fin.last n)-z 0|) := by
  cases n with
  | zero => simp [cycleIntegrand, pathIntegrand]
  | succ n =>
    rw [cycleIntegrand, pathIntegrand_product]
    simp only [Fin.prod_univ_succ, Fin.tail, Fin.succ_castSucc, Fin.succ_last, Fin.castSucc_zero]
    ring

/-- Cyclic multiple integrals are absolutely convergent at every positive integer order.
Use: justifies the final product-space Fubini conversion for the spectral moments.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: the absolute cycle integrand is at most the integrable product of |m|. -/
theorem cycleIntegrand_integrable {m : ℝ → ℝ} (hm : Integrable m) (hmm : Measurable m)
    (n : ℕ) : Integrable (cycleIntegrand m n) := by
  -- Each cycle link has modulus at most one, leaving an independent-coordinate majorant.
  have h : Integrable (fun z : Fin (n+1) → ℝ => ∏ i, |m (z i)|) :=
    Integrable.fintype_prod (fun _ => hm.abs)
  apply h.mono'
  · exact ((hmm.comp (measurable_pi_apply 0)).mul
      (pathIntegrand_measurable hmm n (measurable_pi_apply 0) (measurable_pi_apply 0)
        (fun i => measurable_pi_apply i.succ))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, cycleIntegrand, abs_mul, Fin.prod_univ_succ]
      exact mul_le_mul_of_nonneg_left (pathIntegrand_bound m n (z 0) (z 0) (Fin.tail z))
        (abs_nonneg _)

/-- Every spectral moment is the literal Lebesgue multiple integral on R^(n+1).
Use: the full product-integral form of all G_p constraints in the continuum relaxation.
Article: jacobi, Appendix D.1 (strict concentration gain).
Proof: absolute convergence licenses Fubini; integrate the open path and use the
proved nested cyclic spectral formula for the same actual kernel operator. -/
theorem moment_multiple_integral {m : ℝ → ℝ} (hm : Integrable m) (hmm : Measurable m)
    (hn : ∀ x, 0 ≤ m x) (n : ℕ) :
    (∑' j, chebyshev2.Continuum.kernelEigenvalue hm hn j^(n+1)) =
      ∫ z : Fin (n+1) → ℝ, cycleIntegrand m n z := by
  -- Fubini and the path identity recover the already identified operator moment.
  rw [moment_cycle hm hn (by omega : 0 < n+1),
    integral_fin_cons _ (cycleIntegrand_integrable hm hmm n)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    simp only [cycleIntegrand, Fin.cons_zero, Fin.tail_cons, integral_const_mul, Nat.add_sub_cancel]
    rw [path_integral hm hmm]


end
end jacobi.Continuum
