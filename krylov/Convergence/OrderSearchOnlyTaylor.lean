import krylov.Convergence.OrderSearchOnlyJets
import krylov.Convergence.OneGradientOutputTaylor
import krylov.Methods.FiniteOracleCharts

/-!
Article: main_krylov, thm:D and lem:cycle-transfer, actual search-only output Taylor calculus.
Use: the full true initial-gradient/operator finite source is substituted
in the actual raw-policy output, with a uniform true Taylor remainder.
Its leading coefficient is the genuine derivative of the real executor.
Source: primitive policy regularity and compact finite-order Taylor calculus.
-/
namespace krylov.Convergence
noncomputable section
open Set Metric krylov.Methods krylov.Reference krylov.Functions krylov.Stability
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The genuine terminal-gradient map in finite independent raw source coordinates.
Article: main_krylov, thm:D, DC. -/
def searchOnlyFiniteTerminal (m : ProbedMethod E) (Q : E →L[ℝ] E) (N : ℕ)
    (z : E × (Fin N → E →L[ℝ] E)) : E :=
  probedGradient m (fcFiniteOperatorPath Q N z.2) (fcFiniteOperatorPath Q N z.2) z.1 N

/-- Original primitive smooth-policy hypotheses derive true C-two output
regularity in all genuine finite coordinates. Article: thm:D and lem:U. -/
theorem searchOnlyFiniteTerminal_contDiffAt
    (m : ProbedMethod E) (hc : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v,v≠0 →0 < inner ℝ v (Q v)) (N : ℕ) (g : E)
    (hpre : ∀ i<N,CG.gradient Q g i≠0) (hs : SmoothProbedCycleAt m 2 Q g N) :
    ContDiffAt ℝ 2 (searchOnlyFiniteTerminal m Q N) (g,0) := by
  let A:=fun z : E × (Fin N → E →L[ℝ] E)=>fcFiniteOperatorPath Q N z.2
  have hA j : ContDiffAt ℝ 2 (fun z=>A z j) (g,0) :=
    (fcFiniteOperatorPath_analytic Q N j (g,0)).contDiffAt
  exact smoothProbed_gradient_regular m hc A A Prod.fst (g,0) N
    (fun j _=>hA j) (fun j _=>hA j) contDiffAt_fst Q
    (fcFiniteOperatorPath_zero Q N) (fcFiniteOperatorPath_zero Q N) hQ hpos hpre hs

/-- The actual full quadratic reference output vanishes for every true
initial gradient, including terminated references. Article: thm:D. -/
theorem searchOnlyFiniteTerminal_reference_zero
    (m : ProbedMethod E) (hc : CGConsistent m)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v,v≠0 →0 < inner ℝ v (Q v)) (g : E) :
    searchOnlyFiniteTerminal m Q (Module.finrank ℝ E) (g,0)=0 := by
  rw [searchOnlyFiniteTerminal,fcFiniteOperatorPath_zero,probedGradient,
    quadratic_gradient_eq_cg m hc Q hQ hpos]
  exact cg_gradient_finrank_zero Q hQ hpos g

/-- The true native terminal map has a compact full quadratic Taylor tube.
Article: main_krylov, thm:D and lem:cycle-transfer. -/
theorem compact_searchOnly_output_taylor
    (m : ProbedMethod E) (Q : E →L[ℝ] E) (N : ℕ) (K : Set E) (hK : IsCompact K)
    (hreg : ∀ g∈K,ContDiffAt ℝ 2 (searchOnlyFiniteTerminal m Q N) (g,0))
    (hzero : ∀ g∈K,searchOnlyFiniteTerminal m Q N (g,0)=0) :
    ∃ δ C M : ℝ,0<δ ∧0≤C ∧0<M ∧
      (∀ g∈K,‖fderiv ℝ (searchOnlyFiniteTerminal m Q N) (g,0)‖≤M) ∧
      ∀ g∈K,∀ z : E × (Fin N → E →L[ℝ] E),‖z‖≤δ →
        ‖searchOnlyFiniteTerminal m Q N ((g,0)+z)-
          fderiv ℝ (searchOnlyFiniteTerminal m Q N) (g,0) z‖≤C*‖z‖^2 := by
  let F := searchOnlyFiniteTerminal m Q N
  let K₀ := K ×ˢ {(0 : Fin N → E →L[ℝ] E)}
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
theorem searchOnly_output_source_transfer
    (m : ProbedMethod E) (Q : E →L[ℝ] E) (N : ℕ) (U : Set E)
    (I : ℝ → E → E × (Fin N → E →L[ℝ] E))
    (J : E → E × (Fin N → E →L[ℝ] E))
    (K : Set E) (hK : IsCompact K) (hKU : ∀ u∈U,Q u∈K)
    (hreg : ∀ g∈K,ContDiffAt ℝ 2 (searchOnlyFiniteTerminal m Q N) (g,0))
    (hzero : ∀ g∈K,searchOnlyFiniteTerminal m Q N (g,0)=0)
    (S : ℝ) (hS : 0<S)
    (hsize : ∃ es : ℝ,0<es ∧∀ ε : ℝ,0<ε →ε<es →∀ u∈U,‖I ε u‖≤S*ε)
    (hjet : ∀ η : ℝ,0<η →∃ ej : ℝ,0<ej ∧∀ ε : ℝ,0<ε →ε<ej →∀ u∈U,‖I ε u-ε • J u‖≤η*ε) :
    ∀ η : ℝ,0<η →∃ ep : ℝ,0<ep ∧∀ ε : ℝ,0<ε →ε<ep →∀ u∈U,
      ‖ε • searchOnlyFiniteTerminal m Q N ((Q u,0)+I ε u)-
        ε^2 • fderiv ℝ (searchOnlyFiniteTerminal m Q N) (Q u,0) (J u)‖≤η*ε^2 := by
  obtain ⟨δ,C,M,hδ,hC,hM,hder,htaylor⟩ := compact_searchOnly_output_taylor m Q N K hK hreg hzero
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
  let L := fderiv ℝ (searchOnlyFiniteTerminal m Q N) (Q u,0)
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
  have heq : ε • searchOnlyFiniteTerminal m Q N ((Q u,0)+I ε u)-ε^2 • L (J u)=
      ε • ((searchOnlyFiniteTerminal m Q N ((Q u,0)+I ε u)-L (I ε u))+
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
