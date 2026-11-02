import krylov.Tensor.CubicBanach
import krylov.Tensor.Symmetrization

/-!
Article: main_krylov, thm:Hp, the actual continuous multilinear cubic dictionary.
Use: connect the already proved Banach identity for curried symmetric cubic
forms to mathlib's multilinear operator norm and projective tensor duality.
Source: mathlib's isometric currying equivalences, with Banach (1938).
-/

namespace krylov.Tensor
noncomputable section
open ContinuousMultilinearMap
open scoped TensorProduct BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual curried trilinear map of a genuine continuous three-slot form.
Article: main_krylov, thm:Hp.
Use: isometric currying only; no coefficient array or norm equality is assumed. -/
def cubicCurried (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) :
    E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  let c₁ := (continuousMultilinearCurryFin1 ℝ E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  let c₂ := (c₁.postcomp E).comp
    (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin 2 => E) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  c₂.comp f.curryLeft

/-- The true curried evaluation is exactly the original three-slot evaluation.
Article: main_krylov, thm:Hp. Proof: the actual currying evaluation identities. -/
theorem cubicCurried_apply (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (x y z : E) : cubicCurried f x y z = f ![x, y, z] := by
  change f (Fin.cons x (Fin.cons y (Fin.snoc 0 z))) = f ![x, y, z]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- Slot-invariant genuine multilinear forms define actual symmetric curried cubics.
Article: main_krylov, thm:Hp.
Proof: transpositions of slots zero/one and one/two give the two defining symmetries. -/
def symmetricCubicOfMultilinear (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (hf : IsSymmetricForm f) : krylov.Functions.SymmetricCubic E where
  form := cubicCurried f
  swap₁ := by
    intro x y z
    rw [cubicCurried_apply, cubicCurried_apply]
    have h := congrArg (fun g : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ => g ![x, y, z])
      (hf (Equiv.swap (0 : Fin 3) 1))
    have hv : (fun i : Fin 3 => ![x, y, z] ((Equiv.swap (0 : Fin 3) 1) i)) = ![y, x, z] := by
      ext i
      fin_cases i <;> norm_num [Equiv.swap_apply_def]
    change f (fun i : Fin 3 => ![x, y, z] ((Equiv.swap (0 : Fin 3) 1) i)) = f ![x, y, z] at h
    rw [hv] at h
    exact h.symm
  swap₂ := by
    intro x y z
    rw [cubicCurried_apply, cubicCurried_apply]
    have h := congrArg (fun g : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ => g ![x, y, z])
      (hf (Equiv.swap (1 : Fin 3) 2))
    have hv : (fun i : Fin 3 => ![x, y, z] ((Equiv.swap (1 : Fin 3) 2) i)) = ![x, z, y] := by
      ext i
      fin_cases i <;> norm_num [Equiv.swap_apply_def]
    change f (fun i : Fin 3 => ![x, y, z] ((Equiv.swap (1 : Fin 3) 2) i)) = f ![x, y, z] at h
    rw [hv] at h
    exact h.symm

/-- For genuine symmetric cubic forms the diagonal spectral ball is exactly the true multilinear operator ball.
Article: main_krylov, thm:Hp.
Proof: one direction restricts the actual operator bound to a repeated unit
vector; the converse is the proved Banach identity transported by actual
currying, including zero vectors and trivial spaces. -/
theorem symmetric_cubic_norm_le_iff [FiniteDimensional ℝ E]
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) (hf : IsSymmetricForm f)
    {C : ℝ} (hC : 0 ≤ C) :
    ‖f‖ ≤ C ↔ ∀ x : E, ‖x‖ = 1 → |f (fun _ : Fin 3 => x)| ≤ C := by
  constructor
  · intro h x hx
    have hb := f.le_opNorm (fun _ : Fin 3 => x)
    simp only [Real.norm_eq_abs, hx, Finset.prod_const_one, mul_one] at hb
    exact hb.trans h
  · intro hdiag
    let T := symmetricCubicOfMultilinear f hf
    have hd (x : E) (hx : ‖x‖ = 1) : |T.form x x x| ≤ C := by
      rw [show T.form x x x = f ![x, x, x] from cubicCurried_apply f x x x]
      have hv : (![x, x, x] : Fin 3 → E) = fun _ => x := by ext i; fin_cases i <;> rfl
      rw [hv]
      exact hdiag x hx
    apply f.opNorm_le_bound hC
    intro m
    have hb := cubic_diagonal_bound T C hd (m 0) (m 1) (m 2)
    have he : T.form (m 0) (m 1) (m 2) = f m := by
      rw [show T.form (m 0) (m 1) (m 2) = f ![m 0, m 1, m 2] from
        cubicCurried_apply f (m 0) (m 1) (m 2)]
      congr 1
      ext i
      fin_cases i <;> rfl
    rw [he] at hb
    simpa only [Real.norm_eq_abs, Fin.prod_univ_three, mul_assoc] using hb

/-- The actual symmetric cubic spectral unit ball has the genuine attained nuclear support.
Article: main_krylov, thm:Hp, the spectral/nuclear tensor identity.
Proof: Banach identifies the original diagonal spectral constraint with the
true multilinear norm; the actual projective Hahn--Banach duality then gives
the attained nuclear norm of the symmetrized target tensor. -/
theorem symmetric_cubic_nuclear_duality [FiniteDimensional ℝ E]
    (X : ⨂[ℝ] _ : Fin 3, E) :
    IsGreatest ((fun f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ =>
      PiTensorProduct.lift f.toMultilinearMap (tensorSymmetrization X)) ''
        {f | IsSymmetricForm f ∧ ∀ x : E, ‖x‖ = 1 → |f (fun _ : Fin 3 => x)| ≤ 1})
      ‖tensorSymmetrization X‖ := by
  have hs : {f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ |
        IsSymmetricForm f ∧ ∀ x : E, ‖x‖ = 1 → |f (fun _ : Fin 3 => x)| ≤ 1} =
      {f | ‖f‖ ≤ 1 ∧ IsSymmetricForm f} := by
    ext f
    constructor
    · rintro ⟨hf, hd⟩
      exact ⟨(symmetric_cubic_norm_le_iff f hf (by norm_num)).mpr hd, hf⟩
    · rintro ⟨hn, hf⟩
      exact ⟨hf, (symmetric_cubic_norm_le_iff f hf (by norm_num)).mp hn⟩
  rw [hs]
  exact symmetric_projective_duality X

/-- Any nonnegative cubic spectral budget scales the genuine attained nuclear support exactly.
Article: main_krylov, thm:Hp, including the printed budget two.
Proof: scale an actual unit-ball norming form for attainment; the genuine
multilinear norm estimate gives the upper bound for every admissible form. -/
theorem symmetric_cubic_nuclear_support [FiniteDimensional ℝ E]
    (X : ⨂[ℝ] _ : Fin 3, E) {C : ℝ} (hC : 0 ≤ C) :
    IsGreatest ((fun f : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ =>
      PiTensorProduct.lift f.toMultilinearMap (tensorSymmetrization X)) ''
        {f | IsSymmetricForm f ∧ ∀ x : E, ‖x‖ = 1 → |f (fun _ : Fin 3 => x)| ≤ C})
      (C * ‖tensorSymmetrization X‖) := by
  obtain ⟨f, ⟨hf, hd⟩, he⟩ := (symmetric_cubic_nuclear_duality X).1
  have hs : IsSymmetricForm (C • f) := by
    intro σ
    change (domDomCongrₗᵢ ℝ E ℝ σ) (C • f) = C • f
    rw [_root_.map_smul]
    exact congrArg (fun g => C • g) (hf σ)
  have hn : ‖C • f‖ ≤ C := by
    rw [norm_smul, Real.norm_of_nonneg hC]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      ((symmetric_cubic_norm_le_iff f hf (by norm_num)).mpr hd) hC
  have hdC := (symmetric_cubic_norm_le_iff (C • f) hs hC).mp hn
  refine ⟨⟨C • f, ⟨hs, hdC⟩, ?_⟩, ?_⟩
  · change PiTensorProduct.lift (C • f).toMultilinearMap (tensorSymmetrization X) =
      C * ‖tensorSymmetrization X‖
    change (PiTensorProduct.liftIsometry ℝ (fun _ : Fin 3 => E) ℝ (C • f))
      (tensorSymmetrization X) = C * ‖tensorSymmetrization X‖
    rw [_root_.map_smul, smul_apply, smul_eq_mul, PiTensorProduct.liftIsometry_apply_apply]
    exact congrArg (fun v => C * v) he
  · rintro v ⟨g, ⟨hg, hdg⟩, rfl⟩
    have hng := (symmetric_cubic_norm_le_iff g hg hC).mpr hdg
    calc
      _ ≤ ‖PiTensorProduct.lift g.toMultilinearMap (tensorSymmetrization X)‖ := le_abs_self _
      _ ≤ ‖g‖ * ‖tensorSymmetrization X‖ := PiTensorProduct.norm_eval_le_projectiveSeminorm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hng (norm_nonneg _)

end
end krylov.Tensor
