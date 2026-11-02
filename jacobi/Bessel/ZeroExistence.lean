import jacobi.Bessel.Wave

/-!
Article: jacobi, Proposition B.1.
The actual Bessel wave oscillates beyond every finite radius. Consequently
the original entire function has unboundedly many positive real spectral
zeros. No pre-existing enumeration or asymptotic expansion is assumed.
Source: Sturm oscillation proved here from the restoring equation and the mean value theorem.
Use: discharges the coefficient bound of the oscillation theorem for every real order alpha>-1.
-/
namespace jacobi.Bessel
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- Beyond an explicit finite radius the genuine Bessel wave has a uniformly positive restoring coefficient.
Use: discharges the coefficient bound of the oscillation theorem for every real order alpha>-1.
Article: jacobi, Theorem 2.1.
Proof: x>=2*(alpha^2+1) bounds the inverse-square perturbation by one half. -/
theorem wave_restoring_bound (a : ℝ) {x : ℝ} (hx : 2*(a^2+1)≤x) :
    1/2≤1+(1/4-a^2)/x^2 := by
  have hxpos : 0<x := by nlinarith [sq_nonneg a]
  have hdiv : (-1/2:ℝ)≤(1/4-a^2)/x^2 :=
    (le_div_iff₀ (sq_pos_of_pos hxpos)).mpr (by nlinarith [sq_nonneg (x-1)])
  linarith

/-- The actual positive-axis Bessel wave has a genuine zero beyond every prescribed radius.
Use: proves existence and infinitude of the source Bessel zero sequence before any McMahon expansion.
Article: jacobi, Theorem 2.1.
Proof: start past the requested radius and the explicit inverse-square
threshold. Both actual derivatives and the exact wave equation satisfy
the proved restoring-oscillation theorem with coefficient at least one half. -/
theorem wave_zero_above {a : ℝ} (ha : -1<a) (B : ℝ) :
    ∃ x:ℝ,B<x ∧ 0<x ∧ normalized (a:ℂ) ((x^2:ℝ):ℂ)=0 := by
  -- The construction is independent of the as yet unproved large-zero asymptotic formula.
  let R := max (B+1) (2*(a^2+1))
  have hxpos : ∀ x∈Ici R,0<x := by
    intro x hx
    have hR : 2*(a^2+1)≤R := le_max_right _ _
    exact lt_of_lt_of_le (by nlinarith [sq_nonneg a]) (hR.trans hx)
  obtain ⟨x,hx,hzero⟩ := restoring_has_zero (R := R) (c := (1/2:ℝ)) (by norm_num)
    (fun x hx => wave_hasDerivAt a (hxpos x hx))
    (fun x hx => waveSlope_hasDerivAt a (hxpos x hx))
    (fun x hx => wave_equation ha (hxpos x hx))
    (fun x hx => wave_restoring_bound a ((le_max_right _ _).trans hx))
  refine ⟨x,?_,hxpos x hx,(wave_zero_iff a (hxpos x hx)).mp hzero⟩
  have hR : B+1≤R := le_max_left _ _
  linarith [hR.trans hx]

/-- The real spectral zero set of the actual normalized entire Bessel function.
Use: defines the genuine squared edge spectrum before its increasing enumeration.
Article: jacobi, Theorem 2.1.
-/
def spectralZeros (a : ℝ) : Set ℝ := {x | normalized (a:ℂ) (x:ℂ)=0}

/-- Every member of the genuine spectral zero set is strictly positive.
Use: bounds initial zero segments and fixes the first spectral zero away from the origin.
Article: jacobi, Theorem 2.1.
Proof: the already proved complex zero-location theorem identifies the given real argument with a positive real. -/
theorem spectralZero_pos {a : ℝ} (ha : -1<a) {x : ℝ} (hx : x∈spectralZeros a) : 0<x := by
  obtain ⟨r,hr,he⟩ := normalized_zero_positive ha hx
  exact (Complex.ofReal_injective he) ▸ hr

/-- The actual spectral zero set is unbounded above.
Use: supplies a genuine successor zero for increasing enumeration and excludes a finite spectrum.
Article: jacobi, Theorem 2.1.
Proof: choose a wave zero past both the requested bound and one. Its
positive squared argument is still larger and is an actual entire-function zero. -/
theorem spectralZero_above {a : ℝ} (ha : -1<a) (B : ℝ) :
    ∃ x∈spectralZeros a,B<x := by
  obtain ⟨x,hx,hp,hzero⟩ := wave_zero_above ha (max B 1)
  refine ⟨x^2,hzero,?_⟩
  have hB := lt_of_le_of_lt (le_max_left B 1) hx
  have h1 := lt_of_le_of_lt (le_max_right B 1) hx
  nlinarith [sq_nonneg (x-1)]

/-- The actual Bessel spectral zero set is infinite for every order alpha>-1.
Use: the source positive Bessel sequence enumerates a genuine infinite set.
Article: jacobi, Theorem 2.1.
Proof: a finite real zero set would be bounded above, contradicting the
proved existence of a genuine spectral zero beyond every real bound. -/
theorem spectralZeros_infinite {a : ℝ} (ha : -1<a) : (spectralZeros a).Infinite := by
  intro hf
  obtain ⟨B,hB⟩ := hf.bddAbove
  obtain ⟨x,hx,hBx⟩ := spectralZero_above ha B
  exact (not_lt_of_ge (hB hx)) hBx

end
end jacobi.Bessel
