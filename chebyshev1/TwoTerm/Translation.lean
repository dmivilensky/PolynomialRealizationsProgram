import chebyshev1.Perturbations.ObjectivePointwise

/-! Translation of the actual nonlinear recurrence and of its derivative data.
Only the coefficients used before the stated horizon need preserve constants.
The initial update already has its canonical one-gradient form. -/
namespace chebyshev1.TwoTerm
noncomputable section
variable {d : Type*}

/-- The actual physical run, translated by an arbitrary center, is exactly
the recurrence driven by the translated oracle. No stationarity is needed. -/
theorem nonlinearError_translate_upto (S : TwoTerm) (g : (d → ℝ) → d → ℝ)
    (a e0 : d → ℝ) {N : ℕ}
    (hfixed : ∀ s, 0 < s → s < N → S.a s + S.b s = 1)
    (n : ℕ) (hn : n ≤ N) :
    S.nonlinearError g (a+e0) n - a =
      S.nonlinearError (fun e => g (a+e)) e0 n := by
  have he : ∀ n, n ≤ N → S.nonlinearError g (a+e0) n =
      a + S.nonlinearError (fun e => g (a+e)) e0 n := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => intro _; rfl
    | one =>
      intro _
      simp only [nonlinearError]
      abel
    | more n ih0 ih1 =>
      intro hn
      rw [nonlinearError, nonlinearError, ih0 (by omega), ih1 (by omega)]
      have hc : S.a (n+1) • a + S.b (n+1) • a = a := by
        rw [← add_smul, hfixed (n+1) (by omega) (by omega), one_smul]
      calc
        _ = (S.a (n+1) • a + S.b (n+1) • a) +
            (S.a (n+1) • S.nonlinearError (fun e => g (a+e)) e0 (n+1) +
              S.b (n+1) • S.nonlinearError (fun e => g (a+e)) e0 n -
              S.gamma (n+1) • g (a + S.nonlinearError (fun e => g (a+e)) e0 (n+1))) := by
          module
        _ = _ := by rw [hc]
  rw [he n hn]
  abel

/-- Translation for an arbitrary finite time of a fixed-point recurrence. -/
theorem nonlinearError_translate (S : TwoTerm) (g : (d → ℝ) → d → ℝ)
    (a e0 : d → ℝ) (hfixed : ∀ s, 0 < s → S.a s + S.b s = 1) (n : ℕ) :
    S.nonlinearError g (a+e0) n - a =
      S.nonlinearError (fun e => g (a+e)) e0 n :=
  S.nonlinearError_translate_upto g a e0 (fun s hs _ => hfixed s hs) n le_rfl

end
end chebyshev1.TwoTerm

namespace chebyshev1.Perturbations
noncomputable section
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The gradient of the translated objective is the translated actual gradient. -/
theorem gradient_translate (f : E → ℝ) (a e : E) :
    gradient (fun x => f (a+x)) e = gradient f (a+e) := by
  simp only [gradient, fderiv_comp_add_left]

/-- Translating coordinates preserves the actual Hessian operator. -/
theorem gradient_derivative_translate (f : E → ℝ) (a e : E) :
    fderiv ℝ (gradient (fun x => f (a+x))) e = fderiv ℝ (gradient f) (a+e) := by
  have he : gradient (fun x => f (a+x)) = fun x => gradient f (a+x) :=
    funext (gradient_translate f a)
  rw [he, fderiv_comp_add_left]

/-- The actual third-derivative tensor of the objective is transported as well. -/
theorem gradient_second_derivative_translate (f : E → ℝ) (a e : E) :
    fderiv ℝ (fderiv ℝ (gradient (fun x => f (a+x)))) e =
      fderiv ℝ (fderiv ℝ (gradient f)) (a+e) := by
  have he : fderiv ℝ (gradient (fun x => f (a+x))) =
      fun x => fderiv ℝ (gradient f) (a+x) :=
    funext (gradient_derivative_translate f a)
  rw [he, fderiv_comp_add_left]

omit [CompleteSpace E] in
/-- Recursive pointwise third differentiability at an arbitrary center gives
the existing origin-centered hypothesis for its translated objective. -/
theorem threeTimesDifferentiableAtZero_translate (f : E → ℝ) (a : E)
    (hfirst : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x)
    (hsecond : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ (fderiv ℝ f) x)
    (hthird : DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ f)) a) :
    ThreeTimesDifferentiableAtZero (fun e => f (a+e)) := by
  have hpre : Tendsto (fun x : E => a+x) (𝓝 0) (𝓝 a) :=
    (continuous_const_add a).tendsto' 0 a (add_zero a)
  have hfd : fderiv ℝ (fun e => f (a+e)) = fun e => fderiv ℝ f (a+e) :=
    funext (fun _ => fderiv_comp_add_left a)
  have hfd2 : fderiv ℝ (fderiv ℝ (fun e => f (a+e))) =
      fun e => fderiv ℝ (fderiv ℝ f) (a+e) := by
    rw [hfd]
    funext e
    exact fderiv_comp_add_left a
  constructor
  · filter_upwards [hpre.eventually hfirst] with e he
    exact (differentiableAt_comp_add_left a).mpr he
  · rw [hfd]
    filter_upwards [hpre.eventually hsecond] with e he
    exact (differentiableAt_comp_add_left a).mpr he
  · rw [hfd2]
    exact (differentiableAt_comp_add_left (𝕜 := ℝ)
      (f := fderiv ℝ (fderiv ℝ f)) (x := (0:E)) a).mpr
      (by simpa only [add_zero] using hthird)

end
end chebyshev1.Perturbations
