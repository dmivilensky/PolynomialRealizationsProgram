import nesterov.Slow.FiniteProgram

/-!
Article: query normalization before Lemma D.3. Positive per-atom changes
preserve all infinitely many inequalities and the single common value charge.
-/
namespace nesterov.Slow
noncomputable section
open scoped BigOperators NNReal
variable {J : Type*} [Fintype J]

def queryG (u p : ℂ) : ℝ := 1-Complex.normSq (p/u)
def queryS (u p : ℂ) : ℝ := 2*(p/u).im

theorem queryG_eq {u : ℂ} (p : ℂ) (hu : u≠0) :
    queryG u p=(Complex.normSq u-Complex.normSq p)/Complex.normSq u := by
  have hn : Complex.normSq u≠0 := (Complex.normSq_pos.mpr hu).ne'
  rw [queryG,Complex.normSq_div]
  field_simp

theorem queryS_eq {u : ℂ} (p : ℂ) (_hu : u≠0) :
    queryS u p=(2*(p*star u).im)/Complex.normSq u := by
  simp only [queryS,Complex.div_im,Complex.star_def,Complex.mul_im,Complex.conj_re,Complex.conj_im]
  ring

theorem query_normalization_iff {w ω : J→ℝ} {U P : J→ℂ} {t C A : ℝ}
    (hU : ∀ j,U j≠0) (hA : 0<A) :
    FiniteProgram (fun j=>w j*Complex.normSq (U j)/A) ω
      (fun j=>queryG (U j) (P j)) (fun j=>queryS (U j) (P j)) t (C/A) ↔
    FiniteProgram w ω (fun j=>Complex.normSq (U j)-Complex.normSq (P j))
      (fun j=>2*(P j*star (U j)).im) t C := by
  simp_rw [queryG_eq _ (hU _),queryS_eq _ (hU _)]
  exact finiteProgram_reweight (fun j=>(Complex.normSq_pos.mpr (hU j)).ne') hA

theorem inverse_query_mass_pos {w : J→ℝ} (hw : ∀ j,0≤w j) (hws : ∑ j,w j=1)
    {U : J→ℂ} (hU : ∀ j,U j≠0) : 0<∑ j,w j/Complex.normSq (U j) := by
  have hwpos : 0<∑ j,w j := by rw [hws];norm_num
  obtain ⟨j,_,hj⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _=>hw j)).mp hwpos
  exact (Finset.sum_pos_iff_of_nonneg (fun j _=>div_nonneg (hw j) (Complex.normSq_nonneg _))).mpr
    ⟨j,Finset.mem_univ _,div_pos hj (Complex.normSq_pos.mpr (hU j))⟩

/-- One fixed latent probability vector corresponds to the prescribed query
probability vector, and the value constant has exactly the same mass scaling. -/
theorem exists_inverse_query_normalization {w ω : J→ℝ} (hw : ∀ j,0≤w j)
    (hws : ∑ j,w j=1) {U P : J→ℂ} (hU : ∀ j,U j≠0) (t C : ℝ) :
    ∃ (v : J→ℝ≥0) (_hv : ∑ j,v j=1) (A : ℝ),0<A ∧
      (∀ j,(v j:ℝ)=w j/Complex.normSq (U j)/A) ∧
      (FiniteProgram (fun j=>(v j:ℝ)) ω (fun j=>Complex.normSq (U j)-Complex.normSq (P j))
        (fun j=>2*(P j*star (U j)).im) t (C/A) ↔
        FiniteProgram w ω (fun j=>queryG (U j) (P j)) (fun j=>queryS (U j) (P j)) t C) := by
  let A := ∑ j,w j/Complex.normSq (U j)
  have hA : 0<A := inverse_query_mass_pos hw hws hU
  let v : J→ℝ≥0 := fun j=>⟨w j/Complex.normSq (U j)/A,
    div_nonneg (div_nonneg (hw j) (Complex.normSq_nonneg _)) hA.le⟩
  have hv : ∑ j,v j=1 := by
    apply NNReal.coe_injective
    push_cast
    change (∑ j,w j/Complex.normSq (U j)/A)=1
    rw [←Finset.sum_div]
    exact div_self hA.ne'
  refine ⟨v,hv,A,hA,fun _=>rfl,?_⟩
  have he := query_normalization_iff (w:=fun j=>(v j:ℝ)) (ω:=ω) (P:=P) hU (A:=1/A) (one_div_pos.mpr hA)
    (t:=t) (C:=C/A)
  have hw' (j : J) : (v j:ℝ)*Complex.normSq (U j)/(1/A)=w j := by
    change (w j/Complex.normSq (U j)/A)*Complex.normSq (U j)/(1/A)=w j
    field_simp [(Complex.normSq_pos.mpr (hU j)).ne',hA.ne']
  have hC : (C/A)/(1/A)=C := by field_simp
  simp only [hw',hC] at he
  exact he.symm


theorem inverse_query_mean {w v : J→ℝ} {U P : J→ℂ} {A : ℝ}
    (hU : ∀ j,U j≠0) (hv : ∀ j,v j=w j/Complex.normSq (U j)/A) :
    (∑ j,v j*(Complex.normSq (U j)-Complex.normSq (P j)))=
      (∑ j,w j*queryG (U j) (P j))/A := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [hv j,queryG_eq _ (hU j)]
  ring

/-- Query-normalized finite witnesses give actual latent probability spectra,
with the strict minimizer margin preserved by the same mass scaling. -/
theorem query_to_latent_feasible {w : J→ℝ} (hw : ∀ j,0≤w j) (hws : ∑ j,w j=1)
    (c : J→Spectral.Frequency) (a : Spectral.SymbolPair) (t C : ℝ)
    (hu : ∀ j,a.u (c j)≠0)
    (hp : FiniteProgram w (fun j=>Real.arccos (c j))
      (fun j=>queryG (a.u (c j)) (a.p (c j))) (fun j=>queryS (a.u (c j)) (a.p (c j))) t C)
    (hs : |C|<∑ j,w j*queryG (a.u (c j)) (a.p (c j))) :
    ∃ (v : J→ℝ≥0) (hv : ∑ j,v j=1) (C' : ℝ),
      Spectral.Feasible a t (Spectral.finiteSpectrum v c hv) C' ∧
      |C'|<Spectral.meanG (Spectral.finiteSpectrum v c hv) a ∧
      ∀ j,0<w j → 0<v j := by
  obtain ⟨v,hv,A,hA,hweights,he⟩ := exists_inverse_query_normalization hw hws hu t C
  refine ⟨v,hv,C/A,?_,?_,?_⟩
  · apply (feasible_iff_finiteProgram v c hv a t (C/A)).mpr
    exact he.mpr hp
  · rw [meanG_finite]
    change |C/A|<∑ j,(v j:ℝ)*(Complex.normSq (a.u (c j))-Complex.normSq (a.p (c j)))
    rw [inverse_query_mean hu hweights,abs_div,abs_of_pos hA]
    exact (div_lt_div_iff_of_pos_right hA).mpr hs
  · intro j hj
    have hvpos : 0<(v j:ℝ) := by
      rw [hweights j]
      exact div_pos (div_pos hj (Complex.normSq_pos.mpr (hu j))) hA
    exact_mod_cast hvpos

end
end nesterov.Slow
