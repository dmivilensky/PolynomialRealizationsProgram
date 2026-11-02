import krylov.Convergence.OneGradientOutputTaylor

/-!
Article: main_krylov, lem:cycle-transfer, thm:V and prop:EL.
Use: combine genuine C-two independent-output regularity with the actual
quadratic source-jet remainder, obtaining a true cubic native remainder.
Source: compact Taylor and positive gradient scaling.
-/
namespace krylov.Convergence
noncomputable section
open Set krylov.Methods krylov.Reference krylov.Functions
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Quadratic input jets and actual C-two semantic policy calculus give
the cubic remainder after positive gradient rescaling. Article: thm:V. -/
theorem oneGradient_output_source_cubic_transfer
    (m : OneGradientMethod E) (Q : E →L[ℝ] E) (N : ℕ) (U : Set E)
    (I : ℝ → E → E × ((Fin N → E →L[ℝ] E) × (E →L[ℝ] E)))
    (J : E → E × ((Fin N → E →L[ℝ] E) × (E →L[ℝ] E)))
    (K : Set E) (hK : IsCompact K) (hKU : ∀ u∈U,Q u∈K)
    (hreg : ∀ g∈K,ContDiffAt ℝ 2 (oneGradientFiniteOutput m Q N) (g,0))
    (hzero : ∀ g∈K,oneGradientFiniteOutput m Q N (g,0)=0)
    (S : ℝ) (hS : 0<S)
    (hsize : ∃ es : ℝ,0<es ∧∀ ε : ℝ,0<ε →ε<es →∀ u∈U,‖I ε u‖≤S*ε)
    (hjet : ∃ ej B : ℝ,0<ej ∧0<B ∧∀ ε : ℝ,0<ε →ε<ej →∀ u∈U,‖I ε u-ε • J u‖≤B*ε^2) :
    ∃ ep C : ℝ,0<ep ∧0<C ∧∀ ε : ℝ,0<ε →ε<ep →∀ u∈U,
      ‖ε • oneGradientFiniteOutput m Q N ((Q u,0)+I ε u)-
        ε^2 • fderiv ℝ (oneGradientFiniteOutput m Q N) (Q u,0) (J u)‖≤C*ε^3 := by
  obtain ⟨δ,C,M,hδ,hC,hM,hder,htaylor⟩ := compact_oneGradient_output_taylor m Q N K hK hreg hzero
  obtain ⟨es,hes,hs⟩ := hsize
  obtain ⟨ej,B,hej,hB,hj⟩ := hjet
  refine ⟨min es (min ej (δ/(S+1))),C*S^2+M*B+1,by positivity,by positivity,?_⟩
  intro ε hε he u hu
  have hsz := hs ε hε (he.trans_le (min_le_left _ _)) u hu
  have hsmall : ‖I ε u‖≤δ := by
    have hh := (lt_div_iff₀ (by positivity : 0<S+1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    exact hsz.trans (by nlinarith only [hh,hε])
  have ht := htaylor (Q u) (hKU u hu) (I ε u) hsmall
  have hjj := hj ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu
  let L := fderiv ℝ (oneGradientFiniteOutput m Q N) (Q u,0)
  have hlin : ‖L (I ε u)-ε • L (J u)‖≤M*(B*ε^2) := by
    rw [←map_smul,←map_sub]
    exact (L.le_opNorm _).trans (mul_le_mul (hder _ (hKU u hu)) hjj (norm_nonneg _) hM.le)
  have ht' : C*‖I ε u‖^2≤C*S^2*ε^2 := by
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsz 2) hC).trans_eq (by ring)
  have heq : ε • oneGradientFiniteOutput m Q N ((Q u,0)+I ε u)-ε^2 • L (J u)=
      ε • ((oneGradientFiniteOutput m Q N ((Q u,0)+I ε u)-L (I ε u))+
        (L (I ε u)-ε • L (J u))) := by
    simp only [smul_add,smul_sub,smul_smul,pow_two]
    module
  rw [heq,norm_smul,Real.norm_of_nonneg hε.le]
  calc
    _ ≤ ε*(C*S^2*ε^2+M*(B*ε^2)) := mul_le_mul_of_nonneg_left
      ((norm_add_le _ _).trans (add_le_add (ht.trans ht') hlin)) hε.le
    _ ≤ (C*S^2+M*B+1)*ε^3 := by nlinarith only [show 0≤ε^3 by positivity]

end
end krylov.Convergence
