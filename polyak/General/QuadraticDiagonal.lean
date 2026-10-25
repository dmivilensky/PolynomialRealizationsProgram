import polyak.Dynamics.Normalization
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! The rate on genuine finite-dimensional quadratics reduces exactly to
the scalar from-rest recurrence. The eigenbasis is constructed by the real
spectral theorem, and its eigenvalues lie in the prescribed curvature
interval. Parseval transfers a uniform scalar estimate without a factor
depending on the dimension. -/

noncomputable section
namespace polyak.General.QuadraticDiagonal
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

abbrev eigenBasis (H : E→ₗ[ℝ]E) (hH : H.IsSymmetric) :
    OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E :=
  hH.eigenvectorBasis rfl

abbrev eigenvalue (H : E→ₗ[ℝ]E) (hH : H.IsSymmetric)
    (i : Fin (Module.finrank ℝ E)) : ℝ := hH.eigenvalues rfl i

theorem eigenvalue_mem (H : E→ₗ[ℝ]E) (hH : H.IsSymmetric) {μ L : ℝ}
    (hlower : ∀ v : E,μ*‖v‖^2 ≤ inner ℝ (H v) v)
    (hupper : ∀ v : E,inner ℝ (H v) v ≤ L*‖v‖^2)
    (i : Fin (Module.finrank ℝ E)) : eigenvalue H hH i∈Icc μ L := by
  have hl := hlower (eigenBasis H hH i)
  have hu := hupper (eigenBasis H hH i)
  have he := hH.apply_eigenvectorBasis rfl i
  change H (eigenBasis H hH i)=eigenvalue H hH i • eigenBasis H hH i at he
  simp only [he,inner_smul_left,starRingEnd_apply,star_trivial,
    real_inner_self_eq_norm_sq,(eigenBasis H hH).norm_eq_one,one_pow,mul_one] at hl hu
  exact ⟨hl,hu⟩

theorem coordinate_apply (H : E→ₗ[ℝ]E) (hH : H.IsSymmetric) (v : E)
    (i : Fin (Module.finrank ℝ E)) :
    (eigenBasis H hH).repr (H v) i=
      eigenvalue H hH i*(eigenBasis H hH).repr v i :=
  hH.eigenvectorBasis_apply_self_apply rfl v i

theorem coordinate_state (H : E→ₗ[ℝ]E) (hH : H.IsSymmetric)
    (α β : ℝ) (v : E) (n : ℕ) (i : Fin (Module.finrank ℝ E)) :
    ((eigenBasis H hH).repr (Dynamics.state H α β v n).1 i,
      (eigenBasis H hH).repr (Dynamics.state H α β v n).2 i)=
    Dynamics.state (fun z : ℝ=>eigenvalue H hH i*z) α β
      ((eigenBasis H hH).repr v i) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hfirst := congrArg Prod.fst ih
    have hsecond := congrArg Prod.snd ih
    dsimp only at hfirst hsecond
    simp only [Dynamics.state,Dynamics.step,map_sub,map_add,map_smul,
      PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,coordinate_apply]
    rw [hfirst,hsecond]

theorem coordinate_iterate (H : E→ₗ[ℝ]E) (hH : H.IsSymmetric)
    (α β : ℝ) (v : E) (n : ℕ) (i : Fin (Module.finrank ℝ E)) :
    (eigenBasis H hH).repr (Dynamics.iterate H α β v n) i=
      Dynamics.iterate (fun z : ℝ=>eigenvalue H hH i*z) α β
        ((eigenBasis H hH).repr v i) n :=
  congrArg Prod.fst (coordinate_state H hH α β v n i)

theorem sum_coordinate_sq (H : E→ₗ[ℝ]E) (hH : H.IsSymmetric) (v : E) :
    (∑ i : Fin (Module.finrank ℝ E),((eigenBasis H hH).repr v i)^2)=‖v‖^2 := by
  simpa only [OrthonormalBasis.repr_apply_apply] using
    (eigenBasis H hH).sum_sq_inner_right v

theorem norm_apply_le (H : E→ₗ[ℝ]E) (hH : H.IsSymmetric) {μ L : ℝ}
    (hμ : 0 ≤ μ) (hlower : ∀ v : E,μ*‖v‖^2 ≤ inner ℝ (H v) v)
    (hupper : ∀ v : E,inner ℝ (H v) v ≤ L*‖v‖^2)
    (hL : 0 ≤ L) (v : E) : ‖H v‖ ≤ L*‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp
  rw [mul_pow,← sum_coordinate_sq H hH (H v),← sum_coordinate_sq H hH v,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [coordinate_apply,mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hi := eigenvalue_mem H hH hlower hupper i
  exact pow_le_pow_left₀ (hμ.trans hi.1) hi.2 2

omit [FiniteDimensional ℝ E] in
/-- Homogeneity of the actual executor includes its zero-momentum startup. -/
theorem iterate_smul (H : E→ₗ[ℝ]E) (α β c : ℝ) (v : E) (n : ℕ) :
    Dynamics.iterate H α β (c • v) n=c • Dynamics.iterate H α β v n := by
  have hs : ∀ n, Dynamics.state H α β (c • v) n=
      (c • (Dynamics.state H α β v n).1,c • (Dynamics.state H α β v n).2) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [Dynamics.state,ih,Dynamics.step,map_smul]
      congr 1
      module
  exact congrArg Prod.fst (hs n)

theorem scalar_iterate_eq_mul (lam α β u : ℝ) (n : ℕ) :
    Dynamics.iterate (fun z : ℝ=>lam*z) α β u n=
      u*Dynamics.iterate (fun z : ℝ=>lam*z) α β 1 n := by
  let H : ℝ→ₗ[ℝ]ℝ := LinearMap.mul ℝ ℝ lam
  change Dynamics.iterate H α β u n=u*Dynamics.iterate H α β 1 n
  simpa only [smul_eq_mul,mul_one] using iterate_smul H α β u 1 n

omit [FiniteDimensional ℝ E] in
theorem isotropic_iterate (lam α β : ℝ) (v : E) (n : ℕ) :
    Dynamics.iterate (fun x : E=>lam • x) α β v n=
      Dynamics.iterate (fun z : ℝ=>lam*z) α β 1 n • v := by
  have hs : ∀ n,Dynamics.state (fun x : E=>lam • x) α β v n=
      ((Dynamics.state (fun z : ℝ=>lam*z) α β 1 n).1 • v,
        (Dynamics.state (fun z : ℝ=>lam*z) α β 1 n).2 • v) := by
    intro n
    induction n with
    | zero => simp only [Dynamics.state,one_smul]
    | succ n ih =>
      simp only [Dynamics.state,ih,Dynamics.step,smul_eq_mul]
      congr 1
      module
  exact congrArg Prod.fst (hs n)

/-- One uniform scalar estimate transfers to every real symmetric Hessian,
with exactly the same constant in every finite dimension. -/
theorem norm_iterate_le (H : E→ₗ[ℝ]E) (hH : H.IsSymmetric) {μ L M : ℝ}
    (hlower : ∀ v : E,μ*‖v‖^2 ≤ inner ℝ (H v) v)
    (hupper : ∀ v : E,inner ℝ (H v) v ≤ L*‖v‖^2)
    (hM : 0 ≤ M) (α β : ℝ) (n : ℕ)
    (hscalar : ∀ lam ∈ Icc μ L,
      ‖Dynamics.iterate (fun z : ℝ=>lam*z) α β 1 n‖ ≤ M) (v : E) :
    ‖Dynamics.iterate H α β v n‖ ≤ M*‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mp
  rw [mul_pow,← sum_coordinate_sq H hH (Dynamics.iterate H α β v n),
    ← sum_coordinate_sq H hH v,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [coordinate_iterate,scalar_iterate_eq_mul,mul_pow]
  rw [mul_comm ((((eigenBasis H hH).repr v) i)^2)]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hi := hscalar (eigenvalue H hH i) (eigenvalue_mem H hH hlower hupper i)
  have hs := (sq_le_sq₀ (norm_nonneg _) hM).mpr hi
  simpa only [Real.norm_eq_abs,sq_abs] using hs

omit [FiniteDimensional ℝ E] in
/-- The actual affine gradient field is centered at the quadratic's genuine
minimizer before spectral decomposition; the initialization is unchanged. -/
theorem iterate_centered (H : E→ₗ[ℝ]E) (g : E→E) (a : E)
    (hg : ∀ x,g x=H (x-a)) (α β : ℝ) (v : E) (n : ℕ) :
    Dynamics.iterate g α β v n-a=Dynamics.iterate H α β (v-a) n := by
  have ht := Dynamics.iterate_translate g H a α β
    (fun e=>by rw [hg,add_sub_cancel_left]) (v-a) n
  simpa only [add_sub_cancel,add_sub_cancel_left] using congrArg (fun z=>z-a) ht

theorem coordinate_iterate_centered (H : E→ₗ[ℝ]E) (hH : H.IsSymmetric)
    (g : E→E) (a : E) (hg : ∀ x,g x=H (x-a))
    (α β : ℝ) (v : E) (n : ℕ) (i : Fin (Module.finrank ℝ E)) :
    (eigenBasis H hH).repr (Dynamics.iterate g α β v n-a) i=
      (eigenBasis H hH).repr (v-a) i*
        Dynamics.iterate (fun z : ℝ=>eigenvalue H hH i*z) α β 1 n := by
  rw [iterate_centered H g a hg,coordinate_iterate,scalar_iterate_eq_mul]

theorem norm_iterate_centered_le (H : E→ₗ[ℝ]E) (hH : H.IsSymmetric)
    {μ L M : ℝ} (hlower : ∀ v : E,μ*‖v‖^2 ≤ inner ℝ (H v) v)
    (hupper : ∀ v : E,inner ℝ (H v) v ≤ L*‖v‖^2)
    (g : E→E) (a : E) (hg : ∀ x,g x=H (x-a))
    (hM : 0 ≤ M) (α β : ℝ) (n : ℕ)
    (hscalar : ∀ lam ∈ Icc μ L,
      ‖Dynamics.iterate (fun z : ℝ=>lam*z) α β 1 n‖ ≤ M) (v : E) :
    ‖Dynamics.iterate g α β v n-a‖ ≤ M*‖v-a‖ := by
  rw [iterate_centered H g a hg]
  exact norm_iterate_le H hH hlower hupper hM α β n hscalar (v-a)

end polyak.General.QuadraticDiagonal
