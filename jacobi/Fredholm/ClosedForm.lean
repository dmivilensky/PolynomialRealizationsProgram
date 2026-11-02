import jacobi.Fredholm.BranchComparison
import jacobi.Fredholm.AttainedParameters

/-!
Article: jacobi, Theorem D.7.
The three parts of the printed theorem are proved for the actual
quadratures and the actual unrestricted L1 variational infimum.
Every admissible printed candidate is identified with genuine attaining
parameters. No candidate-profile existence, pole-margin or uniqueness
hypothesis is left as an additional assumption.
Source: the direct method, actual Green quadratures and the complete parameter comparison.
Use: identifies arbitrary printed candidates with the parameters of the genuine minimizer.
-/
namespace jacobi.Fredholm
noncomputable section
open Real Set MeasureTheory jacobi.Variational
set_option backward.isDefEq.respectTransparency false

/-- The two printed branches together have at most one admissible parameter pair.
Use: identifies arbitrary printed candidates with the parameters of the genuine minimizer.
Article: jacobi, Theorem D.7.
Proof: two interior pairs coincide by the complete mass-level uniqueness
theorem; two free pairs coincide by strict free determinant monotonicity.
A mixed pair is impossible because the free candidate of no greater
mass has strictly smaller determinant than the interior candidate. -/
theorem admissible_parameters_unique {s M d t c u k : ℝ}
    (htc : admissibleParameters s M d t c) (huk : admissibleParameters s M d u k) :
    t=u ∧ c=k := by
  -- The comparison is between arbitrary actual quadrature roots, not only known optimizers.
  obtain ⟨ht,hc,htD,htM,htsat⟩ := htc
  obtain ⟨hu,hk,huD,huM,husat⟩ := huk
  by_cases hti : t<1
  · by_cases hui : u<1
    · exact interior_root_unique ⟨ht.1,hti⟩ ⟨hu.1,hui⟩ hc hk
        (htsat hti) (husat hui) htD huD
    · have hue : u=1 := le_antisymm hu.2 (not_lt.mp hui)
      subst u
      have hm : mass 1 k≤mass t c := by rw [htsat hti]; exact huM
      have hh := free_determinant_lt_interior ⟨ht.1,hti⟩ hc hk hm
      rw [htD,huD] at hh
      exact (lt_irrefl _ hh).elim
  · have hte : t=1 := le_antisymm ht.2 (not_lt.mp hti)
    subst t
    by_cases hui : u<1
    · have hm : mass 1 c≤mass u k := by rw [husat hui]; exact htM
      have hh := free_determinant_lt_interior ⟨hu.1,hui⟩ hk hc hm
      rw [htD,huD] at hh
      exact (lt_irrefl _ hh).elim
    · have hue : u=1 := le_antisymm hu.2 (not_lt.mp hui)
      subst u
      exact ⟨rfl,free_root_unique hc hk htD huD⟩

/-- The collection of exactly the candidate energies occurring in the printed two-branch minimum.
Use: states the source minimum as an actual least element of the original candidate collection.
Article: jacobi, Theorem D.7.
-/
def candidateEnergies (s M d : ℝ) : Set ℝ :=
  {E | ∃ t c : ℝ,admissibleParameters s M d t c ∧ E=energy t c/(2*s)^(3/2:ℝ)}

/-- Every admissible printed candidate for an edge problem is realized by a genuine variational minimizer with those exact parameters.
Use: proves sufficiency and attainment for arbitrary candidates, without constructing a hypothetical operator family.
Article: jacobi, Theorem D.7.
Proof: the direct method supplies an actual minimizer and its true
quadratures. Complete uniqueness for both branches identifies its
parameters with the arbitrary given candidate, transferring the actual
attainment and unrestricted L1 infimum equality to that candidate. -/
theorem admissible_candidate_realized (Λ : EdgeSpectrum) {s t c : ℝ}
    (hs : 0<s) (hp : s*Λ.value 0<1)
    (hcandidate : admissibleParameters s Λ.mass (target Λ s) t c) :
    ∃ P : Optimizer s Λ.mass (target Λ s),P.tau hs=t ∧ P.chi hs=c ∧
      extendedInfimum s Λ.mass (Λ.fredholm s)=
        ENNReal.ofReal (energy t c/(2*s)^(3/2:ℝ)) := by
  -- All variational existence and spectral-pole hypotheses are discharged from the stated edge data.
  obtain ⟨P,hP,hvalue⟩ := edge_attained_parameters Λ hs hp
  obtain ⟨ht,hc⟩ := admissible_parameters_unique hP hcandidate
  refine ⟨P,ht,hc,?_⟩
  rwa [ht,hc] at hvalue

/-- At least one of the exact two printed Fredholm alternatives always occurs for every admissible edge problem.
Use: discharges the nonemptiness assertion of the closed-form minimum.
Article: jacobi, Theorem D.7.
Proof: a genuine optimizer has physical tau<=1 and the actual
complementarity relation. Split tau<1 from tau=1 and read off its
proved original mass and determinant quadratures. -/
theorem closed_form_alternatives (Λ : EdgeSpectrum) {s : ℝ}
    (hs : 0<s) (hp : s*Λ.value 0<1) :
    (∃ t c : ℝ,t∈Ioo (0:ℝ) 1 ∧ c∈Ioo (0:ℝ) 1 ∧
      mass t c=s*Λ.mass ∧ determinant t c=target Λ s) ∨
    (∃ c : ℝ,c∈Ioo (0:ℝ) 1 ∧ determinant 1 c=target Λ s ∧ mass 1 c≤s*Λ.mass) := by
  -- The alternatives come from an actual minimizer rather than a formal parameter dichotomy.
  obtain ⟨P,hP,_⟩ := edge_attained_parameters Λ hs hp
  obtain ⟨ht,hc,hD,hM,hsat⟩ := hP
  by_cases hti : P.tau hs<1
  · exact Or.inl ⟨P.tau hs,P.chi hs,⟨ht.1,hti⟩,hc,hsat hti,hD⟩
  · have he : P.tau hs=1 := le_antisymm ht.2 (not_lt.mp hti)
    rw [he] at hD hM
    exact Or.inr ⟨P.chi hs,hc,hD,hM⟩

/-- The actual unrestricted Fredholm infimum is exactly the attained minimum of all printed candidate values.
Use: the complete article-facing closed-form calibration, with arbitrary candidates and no extra numerical or profile premises.
Article: jacobi, Theorem D.7.
Proof: an actual optimizer supplies a candidate and its unrestricted
L1 infimum value. Any other candidate has the same parameters by the
complete branch comparison, hence the same energy. The nonempty
candidate collection therefore has this actual value as its least element. -/
theorem fredholm_closed_form (Λ : EdgeSpectrum) {s : ℝ}
    (hs : 0<s) (hp : s*Λ.value 0<1) :
    ∃ t c : ℝ,admissibleParameters s Λ.mass (target Λ s) t c ∧
      IsLeast (candidateEnergies s Λ.mass (target Λ s)) (energy t c/(2*s)^(3/2:ℝ)) ∧
      extendedInfimum s Λ.mass (Λ.fredholm s)=
        ENNReal.ofReal (energy t c/(2*s)^(3/2:ℝ)) := by
  -- Every candidate in the least-element assertion uses the original printed conditions.
  obtain ⟨P,hP,hvalue⟩ := edge_attained_parameters Λ hs hp
  refine ⟨P.tau hs,P.chi hs,hP,⟨⟨P.tau hs,P.chi hs,hP,rfl⟩,?_⟩,hvalue⟩
  intro E hE
  obtain ⟨u,k,huk,hEeq⟩ := hE
  obtain ⟨hu,hk⟩ := admissible_parameters_unique hP huk
  rw [hEeq,← hu,← hk]

end
end jacobi.Fredholm
