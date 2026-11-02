import krylov.Completion.SchurTrialExtension
set_option autoImplicit false
/-!
Article: main_krylov, thm:radau, smooth continuation of interval rules.
Use: prove C-r regularity from primitive observed entries at the genuine
shifted inverse domains, including collapsed feasible intervals.
Source: finite entry calculus, actual Schur contractions and smooth inversion.
-/

namespace krylov.Completion
noncomputable section
open Matrix krylov.LinearAlgebra krylov.Stability
open scoped BigOperators Matrix.Norms.L2Operator
variable {n p : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {r : WithTop ℕ∞}

private theorem schur_entry_contDiff (M : X → Matrix (Fin n) (Fin p) ℝ) (x : X)
    (hM : ContDiffAt ℝ r M x) (i : Fin n) (j : Fin p) :
    ContDiffAt ℝ r (fun z => M z i j) x := by
  have h := (matrixEntryEquiv n p).toContinuousLinearMap.contDiff.contDiffAt.comp x hM
  exact contDiffAt_pi.mp h (i,j)

/-- The real cross-column Schur contraction is exactly its physical vector
quadratic form, without any orthogonal-coordinate choice.
Use: differentiate the actual data-only formulas in their original entries.
Article: main_krylov, thm:radau.
Proof: matrix multiplication reads the true physical cross vector, and the
existing singleton cross-column contraction gives its genuine quadratic form. -/
theorem schur_cross_contraction (S : Matrix (Fin n) (Fin p) ℝ) (d : Fin n → ℝ)
    (M : Matrix (Fin p) (Fin p) ℝ) :
    ((Sᵀ*crossColumn d)ᵀ*M*(Sᵀ*crossColumn d)) 0 0=
      (Sᵀ*ᵥ d) ⬝ᵥ (M*ᵥ (Sᵀ*ᵥ d)) := by
  have he : Sᵀ*crossColumn d=crossColumn (Sᵀ*ᵥ d) := by
    ext i j
    rfl
  rw [he,crossColumn_quadratic]
  rfl

/-- Both original rational Schur endpoints are C-r in their genuine smooth
observed data at the two actual shifted inverse domains.
Use: no ordering, interval-width or feasibility condition is needed for this
local continuation; only the two real determinants enter differentiation.
Article: main_krylov, thm:radau and s8:dcsdef.
Proof: all observed Gram and cross entries are finite smooth sums. Actual
spectral-norm inversion is smooth on the true determinant domains, and the
real cross contraction is a finite smooth scalar quadratic form. -/
theorem contDiff_schur_endpoints (S : X → Matrix (Fin n) (Fin p) ℝ)
    (d : X → Fin n → ℝ) (T : X → Matrix (Fin p) (Fin p) ℝ) (mu upper : ℝ) (x : X)
    (hS : ∀ i j,ContDiffAt ℝ r (fun z => S z i j) x)
    (hd : ∀ i,ContDiffAt ℝ r (fun z => d z i) x)
    (hT : ∀ i j,ContDiffAt ℝ r (fun z => T z i j) x)
    (hlo : (T x-mu • ((S x)ᵀ*S x)).det≠0)
    (hhi : (upper • ((S x)ᵀ*S x)-T x).det≠0) :
    ContDiffAt ℝ r (fun z => schurLowerCurvature (S z) (d z) (T z) mu) x ∧
      ContDiffAt ℝ r (fun z => schurUpperCurvature (S z) (d z) (T z) upper) x := by
  let G := fun z => (S z)ᵀ*S z
  let b := fun z => (S z)ᵀ*ᵥ d z
  have hG (i j : Fin p) : ContDiffAt ℝ r (fun z => G z i j) x := by
    change ContDiffAt ℝ r (fun z => ∑ a : Fin n,S z a i*S z a j) x
    exact ContDiffAt.sum (fun a _ => (hS a i).mul (hS a j))
  have hb (i : Fin p) : ContDiffAt ℝ r (fun z => b z i) x := by
    change ContDiffAt ℝ r (fun z => ∑ a : Fin n,S z a i*d z a) x
    exact ContDiffAt.sum (fun a _ => (hS a i).mul (hd a))
  have hn : ContDiffAt ℝ r (fun z => d z ⬝ᵥ d z) x :=
    ContDiffAt.sum (fun i _ => (hd i).mul (hd i))
  have hMlo : ContDiffAt ℝ r (fun z => T z-mu • G z) x :=
    contDiff_spectral_matrix _ x (fun i j => (hT i j).sub (contDiffAt_const.mul (hG i j)))
  have hMhi : ContDiffAt ℝ r (fun z => upper • G z-T z) x :=
    contDiff_spectral_matrix _ x (fun i j => (contDiffAt_const.mul (hG i j)).sub (hT i j))
  have hIlo := contDiff_spectral_inverse _ x hMlo (isUnit_iff_ne_zero.mpr hlo)
  have hIhi := contDiff_spectral_inverse _ x hMhi (isUnit_iff_ne_zero.mpr hhi)
  have hquad (M : X → Matrix (Fin p) (Fin p) ℝ) (hM : ContDiffAt ℝ r M x) :
      ContDiffAt ℝ r (fun z => b z ⬝ᵥ (M z*ᵥ b z)) x := by
    change ContDiffAt ℝ r (fun z => ∑ i : Fin p,b z i*(∑ j : Fin p,M z i j*b z j)) x
    exact ContDiffAt.sum (fun i _ => (hb i).mul (ContDiffAt.sum
      (fun j _ => (schur_entry_contDiff M x hM i j).mul (hb j))))
  constructor
  · convert! (contDiffAt_const.mul hn).add (contDiffAt_const.mul (hquad _ hIlo)) using 1
    funext z
    rw [schurLowerCurvature,schur_cross_contraction]
  · convert! (contDiffAt_const.mul hn).sub (contDiffAt_const.mul (hquad _ hIhi)) using 1
    funext z
    rw [schurUpperCurvature,schur_cross_contraction]

/-- The arithmetic and harmonic observed-step continuations are C-r at
their true endpoint denominator domains, also for equal endpoints.
Use: smooth native interval estimates require no strictly positive width.
Article: main_krylov, thm:radau and s8:dcsdef.
Proof: compose the proved genuine endpoint calculus with the original scalar
arithmetic/harmonic expressions; only actual nonzero denominators are used. -/
theorem contDiff_schur_rules (S : X → Matrix (Fin n) (Fin p) ℝ)
    (d : X → Fin n → ℝ) (T : X → Matrix (Fin p) (Fin p) ℝ) (q : X → ℝ)
    (mu upper : ℝ) (x : X)
    (hS : ∀ i j,ContDiffAt ℝ r (fun z => S z i j) x)
    (hd : ∀ i,ContDiffAt ℝ r (fun z => d z i) x)
    (hT : ∀ i j,ContDiffAt ℝ r (fun z => T z i j) x) (hq : ContDiffAt ℝ r q x)
    (hlo : (T x-mu • ((S x)ᵀ*S x)).det≠0)
    (hhi : (upper • ((S x)ᵀ*S x)-T x).det≠0)
    (hl : 0<schurLowerCurvature (S x) (d x) (T x) mu)
    (hh : 0<schurUpperCurvature (S x) (d x) (T x) upper) :
    ContDiffAt ℝ r (fun z => schurArithmeticEstimate (S z) (d z) (T z) mu upper (q z)) x ∧
      ContDiffAt ℝ r (fun z => schurHarmonicTrial (S z) (d z) (T z) mu upper (q z)) x := by
  have he := contDiff_schur_endpoints S d T mu upper x hS hd hT hlo hhi
  exact ⟨(hq.mul ((he.1.inv hl.ne').add (he.2.inv hh.ne'))).div_const 2,
    (contDiffAt_const.mul hq).div (he.1.add he.2) (add_pos hl hh).ne'⟩

end
end krylov.Completion
