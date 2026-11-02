import krylov.Convergence.OneGradientSourceJet
import krylov.Stability.CompactSmooth

/-!
Article: main_krylov, lem:cycle-transfer, thm:V and prop:EL.
Use: expand the true finite one-gradient semantic output jointly in the
initial gradient and every real segment operator. The derivative is that
of the actual independent operator executor, not a prescribed response.
Source: compact C-two Taylor calculus for the genuine finite policy.
-/
namespace krylov.Convergence
noncomputable section
open Set krylov.Methods krylov.Reference krylov.Functions krylov.Stability
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Actual semantic one-gradient output in its complete finite source
coordinates. The last operator belongs only to semantics, not the history.
Article: lem:cycle-transfer, thm:V and prop:EL. -/
def oneGradientFiniteOutput (m : OneGradientMethod E) (Q : E →L[ℝ] E) (N : ℕ)
    (z : E × ((Fin N → E →L[ℝ] E) × (E →L[ℝ] E))) : E :=
  m.outputGradient (Q+z.2.2) (oneGradientRun m (fcFiniteOperatorPath Q N z.2.1) z.1 N)

/-- The genuine full output derivative has one common norm bound and one
quadratic Taylor remainder on a compact family of solved quadratic
references. Initial-gradient variations remain part of the real source.
Article: main_krylov, lem:cycle-transfer and thm:V. -/
theorem compact_oneGradient_output_taylor
    (m : OneGradientMethod E) (Q : E →L[ℝ] E) (N : ℕ) (K : Set E) (hK : IsCompact K)
    (hreg : ∀ g∈K,ContDiffAt ℝ 2 (oneGradientFiniteOutput m Q N) (g,0))
    (hzero : ∀ g∈K,oneGradientFiniteOutput m Q N (g,0)=0) :
    ∃ δ C M : ℝ,0<δ ∧0≤C ∧0<M ∧
      (∀ g∈K,‖fderiv ℝ (oneGradientFiniteOutput m Q N) (g,0)‖≤M) ∧
      ∀ g∈K,∀ z : E × ((Fin N → E →L[ℝ] E) × (E →L[ℝ] E)),‖z‖≤δ →
        ‖oneGradientFiniteOutput m Q N ((g,0)+z)-
          fderiv ℝ (oneGradientFiniteOutput m Q N) (g,0) z‖≤C*‖z‖^2 := by
  let F := oneGradientFiniteOutput m Q N
  let K₀ := K ×ˢ {(0 : (Fin N → E →L[ℝ] E) × (E →L[ℝ] E))}
  have hK₀ : IsCompact K₀ := hK.prod isCompact_singleton
  have hF : ∀ z∈K₀,ContDiffAt ℝ 2 F z := by
    rintro ⟨g,θ⟩ ⟨hg,hθ⟩
    have he : θ=0 := hθ
    subst θ
    exact hreg g hg
  obtain ⟨δ,C,hδ,hC,hbound⟩ := compact_smooth_taylor F 2 K₀ hK₀ hF
  have hder : ContinuousOn (fun z=>‖fderiv ℝ F z‖) K₀ :=
    fun z hz=>((hF z hz).continuousAt_fderiv (by norm_num)).norm.continuousWithinAt
  obtain ⟨M,hM⟩ := hK₀.exists_bound_of_continuousOn hder
  refine ⟨δ,C,max M 0+1,hδ,hC,by positivity,?_,?_⟩
  · intro g hg
    have hh := hM (g,0) ⟨hg,rfl⟩
    have hh' : ‖fderiv ℝ F (g,0)‖≤M := (le_abs_self _).trans hh
    exact hh'.trans ((le_max_left M 0).trans (by linarith))
  · intro g hg z hz
    have ht : taylorPolynomial F 2 (g,0) z=fderiv ℝ F (g,0) z := by
      simp only [taylorPolynomial,Finset.sum_range_succ,Finset.sum_range_zero,
        iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply,Nat.factorial_zero,Nat.factorial_one,
        Nat.cast_one,inv_one,one_smul,zero_add,show F (g,0)=0 from hzero g hg]
    simpa only [ht] using hbound (g,0) ⟨hg,rfl⟩ z hz 2 (by decide) le_rfl

/-- A genuine compact output Taylor theorem and a true full source jet
produce the uniform quadratic leading term after actual gradient scaling.
The input hypotheses are analytic source statements, not native rates.
Article: main_krylov, lem:cycle-transfer. -/
theorem oneGradient_output_source_transfer
    (m : OneGradientMethod E) (Q : E →L[ℝ] E) (N : ℕ) (U : Set E)
    (I : ℝ → E → E × ((Fin N → E →L[ℝ] E) × (E →L[ℝ] E)))
    (J : E → E × ((Fin N → E →L[ℝ] E) × (E →L[ℝ] E)))
    (K : Set E) (hK : IsCompact K) (hKU : ∀ u∈U,Q u∈K)
    (hreg : ∀ g∈K,ContDiffAt ℝ 2 (oneGradientFiniteOutput m Q N) (g,0))
    (hzero : ∀ g∈K,oneGradientFiniteOutput m Q N (g,0)=0)
    (S : ℝ) (hS : 0<S)
    (hsize : ∃ es : ℝ,0<es ∧∀ ε : ℝ,0<ε →ε<es →∀ u∈U,‖I ε u‖≤S*ε)
    (hjet : ∀ η : ℝ,0<η →∃ ej : ℝ,0<ej ∧∀ ε : ℝ,0<ε →ε<ej →∀ u∈U,‖I ε u-ε • J u‖≤η*ε) :
    ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε →ε<ep →∀ u∈U,
      ‖ε • oneGradientFiniteOutput m Q N ((Q u,0)+I ε u)-
        ε^2 • fderiv ℝ (oneGradientFiniteOutput m Q N) (Q u,0) (J u)‖≤η*ε^2 := by
  obtain ⟨δ,C,M,hδ,hC,hM,hder,htaylor⟩ := compact_oneGradient_output_taylor m Q N K hK hreg hzero
  intro η hη
  obtain ⟨es,hes,hs⟩ := hsize
  obtain ⟨ej,hej,hj⟩ := hjet (η/(2*(M+1))) (by positivity)
  refine ⟨min es (min ej (min (δ/(S+1)) (η/(2*(C*S^2+1))))),by positivity,?_⟩
  intro ε hε he u hu
  have hsz := hs ε hε (he.trans_le (min_le_left _ _)) u hu
  have hsmall : ‖I ε u‖≤δ := by
    have hh := (lt_div_iff₀ (by positivity : 0<S+1)).mp
      (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    exact hsz.trans (by nlinarith only [hh,hε])
  have ht := htaylor (Q u) (hKU u hu) (I ε u) hsmall
  have hjj := hj ε hε (he.trans_le ((min_le_right _ _).trans (min_le_left _ _))) u hu
  let L := fderiv ℝ (oneGradientFiniteOutput m Q N) (Q u,0)
  have hlin : ‖L (I ε u)-ε • L (J u)‖≤M*(η/(2*(M+1))*ε) := by
    rw [←map_smul,←map_sub]
    exact (L.le_opNorm _).trans (mul_le_mul (hder _ (hKU u hu)) hjj (norm_nonneg _) hM.le)
  have ht' : C*‖I ε u‖^2≤η/2*ε := by
    have hh := (lt_div_iff₀ (by positivity : 0<2*(C*S^2+1))).mp
      (he.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    have hb := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hsz 2) hC
    nlinarith only [hb,mul_nonneg (by positivity : 0≤C*S^2) hε.le,hh,hε,sq_nonneg ε]
  have hl' : M*(η/(2*(M+1))*ε)≤η/2*ε := by
    have hh : 2*(M+1)*(η/(2*(M+1)))=η := by field_simp
    have hm : 0≤η/(2*(M+1))*ε := by positivity
    nlinarith only [congrArg (fun a : ℝ=>a*ε) hh,hm]
  have heq : ε • oneGradientFiniteOutput m Q N ((Q u,0)+I ε u)-ε^2 • L (J u)=
      ε • ((oneGradientFiniteOutput m Q N ((Q u,0)+I ε u)-L (I ε u))+
        (L (I ε u)-ε • L (J u))) := by
    simp only [smul_add,smul_sub,smul_smul,pow_two]
    module
  rw [heq,norm_smul,Real.norm_of_nonneg hε.le]
  calc
    _ ≤ ε*((η/2*ε)+(η/2*ε)) := mul_le_mul_of_nonneg_left
      ((norm_add_le _ _).trans (add_le_add (ht.trans ht') (hlin.trans hl'))) hε.le
    _ = η*ε^2 := by ring

end
end krylov.Convergence
