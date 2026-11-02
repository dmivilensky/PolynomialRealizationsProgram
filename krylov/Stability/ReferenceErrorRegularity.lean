import krylov.Stability.CanonicalRegularity

/-!
Article: main_krylov, thm:C and s4:cor-Q, genuine reference-error regularity.
Use: derive the source penultimate-error normalization and its local and
compact Lipschitz bounds from the actual CG reference recurrence.
Source: true CG prefix analyticity, actual inverse-root regularity and the
existing compact analytic Taylor theorem.
-/

namespace krylov.Stability
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Reference krylov.Secant krylov.Methods
open scoped ContDiff Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}

/-- The genuine canonical reference CG error is analytic in the actual positive base and initial data on its true prefix domain.
Use: prove normalization regularity without assuming moment-denominator or reference-error estimates.
Article: main_krylov, thm:C, lem:U and s4:cor-Q, actual φ regularity.
Proof: the actual CG gradient is analytic through the nonstagnating prefix.
The true varying positive inverse root is analytic on its derived positive
neighborhood; bounded operator evaluation gives the actual canonical error.
-/
theorem referenceCanonicalError_analyticAt
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (x : X) (N : ℕ) (hb : AnalyticAt ℝ base x)
    (hpos : ∀ᶠ y in 𝓝 x, (base y).PosDef) (hg : AnalyticAt ℝ g x)
    (hpre : ∀ i<N, CG.gradient (cgOperator (base x)) (g x) i≠0) :
    AnalyticAt ℝ (fun y => cgCanonicalError (base y) (g y) N) x := by
  -- Differentiate the true reference recurrence and actual metric at the same point.
  have hp := cgOperator_positive (base x) hpos.self_of_nhds
  have hQ : AnalyticAt ℝ (fun y => cgOperator (base y)) x :=
    (matrixOperator_contDiffAt base x hb.contDiffAt).analyticAt
  have hG := (cg_prefix_analytic (fun y => cgOperator (base y)) g x hQ hg hp.1 hp.2 N hpre).1
  have hI : AnalyticAt ℝ (fun y => cgOperator (metricRoot (base y))⁻¹) x :=
    (matrixOperator_contDiffAt _ x (metricRoot_inverse_contDiffAt base x (r := ω) hb.contDiffAt hpos)).analyticAt
  exact analytic_operator_apply hI hG

/-- The actual reference-error norm has a derived first-order local variation bound in the primitive reference parameters.
Use: compare the true own-base normalization on explicit admissible lower scenarios.
Article: main_krylov, thm:C and s4:cor-Q, local Lipschitz variation of φ.
Proof: the actual canonical reference error is analytic, hence has genuine
first-order variation. The reverse norm triangle inequality transfers its
proved vector bound to the real source error norm.
-/
theorem referenceError_norm_order
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (N : ℕ) (hb : AnalyticAt ℝ base 0)
    (hpos : ∀ᶠ y in 𝓝 (0 : X), (base y).PosDef) (hg : AnalyticAt ℝ g 0)
    (hpre : ∀ i<N, CG.gradient (cgOperator (base 0)) (g 0) i≠0) :
    (fun y => ‖cgCanonicalError (base y) (g y) N‖-‖cgCanonicalError (base 0) (g 0) N‖)
      =O[𝓝 (0 : X)] (fun y => ‖y‖) := by
  -- Establish true vector regularity before comparing the source normalization norms.
  have hA := referenceCanonicalError_analyticAt base g 0 N hb hpos hg hpre
  have hB : (fun y => cgCanonicalError (base y) (g y) N-cgCanonicalError (base 0) (g 0) N)
      =O[𝓝 (0 : X)] (fun y => ‖y‖) := by
    simpa only [sub_zero] using hA.differentiableAt.isBigO_sub.norm_right
  have hnorm : (fun y => ‖cgCanonicalError (base y) (g y) N‖-‖cgCanonicalError (base 0) (g 0) N‖)
      =O[𝓝 (0 : X)] (fun y => cgCanonicalError (base y) (g y) N-cgCanonicalError (base 0) (g 0) N) :=
    isBigO_of_le _ fun y => by
      simpa only [Real.norm_eq_abs] using (abs_norm_sub_norm_le
        (cgCanonicalError (base y) (g y) N) (cgCanonicalError (base 0) (g 0) N))
  exact hnorm.trans hB

variable [ProperSpace X]

/-- The genuine reference-error norm has one actual Lipschitz constant and radius over every compatible compact reference set.
Use: derive the compact normalization constant used by the source instance comparison.
Article: main_krylov, thm:C and s4:cor-Q, compact relative-reference regularity of φ.
Proof: actual reference-error analyticity supplies the common compact Taylor
bound at order one. Its true constant Taylor term is the actual reference
error; the reverse norm triangle inequality gives the norm comparison.
-/
theorem compact_referenceError_norm_variation
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (N : ℕ) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K, AnalyticAt ℝ base x)
    (hpos : ∀ x∈K, ∀ᶠ y in 𝓝 x, (base y).PosDef) (hg : ∀ x∈K, AnalyticAt ℝ g x)
    (hpre : ∀ x∈K, ∀ i<N, CG.gradient (cgOperator (base x)) (g x) i≠0) :
    ∃ δ C : ℝ, 0<δ ∧ 0≤C ∧ ∀ x∈K, ∀ h : X, ‖h‖≤δ →
      |‖cgCanonicalError (base (x+h)) (g (x+h)) N‖-‖cgCanonicalError (base x) (g x) N‖|≤C*‖h‖ := by
  -- A single actual compact tube supplies the constant before every reference displacement.
  let f := fun x => cgCanonicalError (base x) (g x) N
  obtain ⟨δ,C,hδ,hC,hT⟩ := compact_analytic_taylor f K hK
    (fun x hx => referenceCanonicalError_analyticAt base g x N (hb x hx) (hpos x hx) (hg x hx) (hpre x hx)) 1
  refine ⟨δ,C,hδ,hC,?_⟩
  intro x hx h hh
  have ht := hT x hx h hh 1 le_rfl le_rfl
  simp only [taylorPolynomial,Finset.sum_range_succ,Finset.sum_range_zero,
    Nat.factorial_zero,Nat.cast_one,inv_one,one_smul,iteratedFDeriv_zero_apply,zero_add,pow_one] at ht
  exact (abs_norm_sub_norm_le _ _).trans ht

end
end krylov.Stability
