import jacobi.Jacobi.FiniteSpectrum
import jacobi.Jacobi.LocalZeros
import jacobi.Bessel.Enumeration

/-!
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
The complete finite spectral zeros are compared with the same actual
Bessel zero set through small-neighborhood existence and compact-gap
exclusion. These are the inputs for fixed-index convergence, with no
assumed finite root ordering or spectral limit.
Source: the proved full finite zero theorem and compact-uniform Mehler--Heine stability.
Use: expresses fixed-index spectral convergence as a sequence indexed by every natural degree.
-/
namespace jacobi.Jacobi
noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual kth squared finite Jacobi zero, with zero padding before that index exists.
Use: expresses fixed-index spectral convergence as a sequence indexed by every natural degree.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
-/
def finiteSigmaAt (a b : ℝ) (ha : -1<a) (hb : -1<b) (n k : ℕ) : ℝ :=
  if hk : k<n then finiteSigma a b ha hb n ⟨k,hk⟩ else 0

/-- Once the requested index exists, the padded finite zero is exactly its genuine ordered finite spectral value.
Use: fixed-index proofs may use actual finite strict ordering without any padding convention.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: unfold the dependent choice with its supplied actual degree inequality. -/
theorem finiteSigmaAt_eq {a b : ℝ} (ha : -1<a) (hb : -1<b) {n k : ℕ} (hk : k<n) :
    finiteSigmaAt a b ha hb n k=finiteSigma a b ha hb n ⟨k,hk⟩ := by
  rw [finiteSigmaAt,dite_eq_left hk]

/-- Every actual enumerated finite squared spectral zero is a zero of the same genuine scaled Jacobi function used in Mehler--Heine.
Use: compact gap exclusion and local complex injectivity apply to the actual canonical finite entries.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: apply the proved exhaustive finite zero equivalence with that index as its witness. -/
theorem finiteSigma_is_zero {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (hn : 0<n) (i : Fin n) :
    normalized (a:ℂ) (b:ℂ) n (1-(finiteSigma a b ha hb n i:ℂ)/(2*(n:ℂ)^2))=0 :=
  (finiteSigma_zero_iff ha hb hn _).mpr ⟨i,rfl⟩

/-- Every genuine Bessel spectral zero is eventually approximated by a canonical finite squared Jacobi zero.
Use: the upper bounds in fixed-index convergence count actual finite spectral entries rather than unindexed zero candidates.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: real Mehler--Heine zero transfer produces a true finite zero.
The complete finite root theorem identifies it with an actual canonical
finite index; the field casts preserve its exact scaled argument. -/
theorem finiteSigma_approximation {a b x ε : ℝ} (ha : -1<a) (hb : -1<b)
    (hx : jacobi.Bessel.normalized (a:ℂ) (x:ℂ)=0) (hε : 0<ε) :
    ∀ᶠ n:ℕ in atTop,∃ i:Fin n,|finiteSigma a b ha hb n i-x|<ε := by
  -- The abstract local zero is identified with its genuine finite index.
  filter_upwards [scaled_zero_approximation (b := b) ha hx hε,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  obtain ⟨z,hz,hzero⟩ := hn
  have he : ((1-z/(2*(n:ℝ)^2):ℝ):ℂ)=1-(z:ℂ)/(2*(n:ℂ)^2) := by push_cast; rfl
  rw [he] at hzero
  obtain ⟨i,hi⟩ := (finiteSigma_zero_iff ha hb hnpos z).mp hzero
  exact ⟨i,hi ▸ hz⟩

/-- A real compact interval containing no genuine Bessel zero eventually contains no actual finite scaled Jacobi zero.
Use: excludes premature finite entries between consecutive limiting spectral zeros.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: the complex embedding of the real interval is compact. Apply
the proved compact nonvanishing theorem to that exact embedded set. -/
theorem finite_zero_exclusion_interval {a b A B : ℝ} (ha : -1<a)
    (hgap : ∀ x∈Icc A B,jacobi.Bessel.normalized (a:ℂ) (x:ℂ)≠0) :
    ∀ᶠ n:ℕ in atTop,∀ x∈Icc A B,
      normalized (a:ℂ) (b:ℂ) n (1-(x:ℂ)/(2*(n:ℂ)^2))≠0 := by
  have h := scaled_nonvanishing_compact (b := (b:ℂ)) (by simpa using ha)
    (isCompact_Icc.image Complex.continuous_ofReal)
    (show ∀ z∈Complex.ofReal '' Icc A B,jacobi.Bessel.normalized (a:ℂ) z≠0 from by
      rintro z ⟨x,hx,rfl⟩
      exact hgap x hx)
  filter_upwards [h] with n hn x hx
  exact hn (x:ℂ) ⟨x,hx,rfl⟩

/-- No actual Bessel spectral zero lies below the first enumerated zero.
Use: identifies the first transferred finite root with the first canonical finite index.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: any such zero belongs to the original real spectral set, whose first enumerated member is least. -/
theorem bessel_nonzero_before_first {a x : ℝ} (ha : -1<a)
    (hx : x< jacobi.Bessel.sigma a ha 0) : jacobi.Bessel.normalized (a:ℂ) (x:ℂ)≠0 := by
  intro hz
  exact (not_lt_of_ge ((jacobi.Bessel.sigma_first ha).2 hz)) hx

/-- No actual Bessel spectral zero lies strictly between two consecutive enumerated zeros.
Use: the finite compact-gap exclusion follows from actual complete Bessel enumeration.
Article: jacobi, Appendix C.6 (uniform shifted spectral convergence).
Proof: any intervening zero would contradict the proved least-successor property. -/
theorem bessel_nonzero_between {a x : ℝ} (ha : -1<a) (k : ℕ)
    (hx : x∈Ioo (jacobi.Bessel.sigma a ha k) (jacobi.Bessel.sigma a ha (k+1))) :
    jacobi.Bessel.normalized (a:ℂ) (x:ℂ)≠0 := by
  intro hz
  have h := (jacobi.Bessel.sigma_successor ha k).2 ⟨hz,hx.1⟩
  linarith [hx.2]

end
end jacobi.Jacobi
