import chebyshev2.Numerics.ContactModels

/-!
Article: chebyshev2, Section 4.1.
Contact Model Sound.
Use: `chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.Panel.inputs_sound` feeds
`chebyshev2.Certificates.Compact.ContactValues.ValidPanel.inputs` (inputs).
Proof chain: `chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement` —
chebyshev2, Theorem 1.2, factor 1.000013; Unconditional uniform gain comparison with the retained
numerical factor.
-/
namespace chebyshev2.Numerics.IntegerCertificate.ContactPolynomial
noncomputable section
open Set Polynomial chebyshev2.Calibration
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
The precise assertion is `Poly.Taylor.Encloses s p.row.inputs x (ContactExpr.values (p.time s
x) (R.normalizedRoot (p.time s x)) (R.normalizedFilter hσ (p.time s x))
(R.normalizedReflectedFilter hσ (p.time s x)) ((Poly.exactPolynomial s p.g).eval x))`.

Use: `chebyshev2.Certificates.Compact.ContactValues.ValidPanel.inputs` uses this assertion
to establish the identity stated in that declaration.

Article: chebyshev2, Theorem 1.2, retained factor 1.000013 via
`chebyshev2.Certificates.Compact.ReferenceBase.uniform_gain_improvement`.

Proof: Use the identities/estimates
`chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.Panel.time_mem`,
`chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.Panel.time_eval`,
`chebyshev2.Numerics.IntegerCertificate.Poly.Rep.at` with the arguments shown in the proof.
-/
theorem Panel.inputs_sound {s : Nat} (hs : 0<s) {piB : Bounds}
    (hpi : piB.Mem s Real.pi) {eL eR : Int} (p : Panel)
    (hc : p.modelCheck s piB eL eR=true) (R : ReferenceData) {σ : ℝ} (hσ : 0<σ)
    (hleft : ∀ t∈Icc (p.left.left s) (p.left.right s),
      |R.normalizedFilter hσ t-p.left.approx s t|≤(eL:ℝ)/s)
    (hright : ∀ v∈Icc (p.right.left s) (p.right.right s),
      |R.normalizedReflectedFilter hσ (2-v)-p.right.approx s v|≤(eR:ℝ)/s)
    (hroot : ∀ t∈Icc (p.left.left s) (p.left.right s),
      |R.normalizedRoot t-(Poly.exactPolynomial s p.left.z).eval
        (p.left.localCoordinate s t)|≤(p.left.delta:ℝ))
    {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    Poly.Taylor.Encloses s p.row.inputs x (ContactExpr.values
      (p.time s x) (R.normalizedRoot (p.time s x))
      (R.normalizedFilter hσ (p.time s x)) (R.normalizedReflectedFilter hσ (p.time s x))
      ((Poly.exactPolynomial s p.g).eval x)) := by
  -- Use the identities/estimates
  -- `chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.Panel.time_mem`,
  -- `chebyshev2.Numerics.IntegerCertificate.ContactPolynomial.Panel.time_eval`,
  -- `chebyshev2.Numerics.IntegerCertificate.Poly.Rep.at` with the arguments shown in the
  -- proof.
  have ht := p.time_mem hs hc hx
  obtain ⟨_,_,_,_,_,_,_,hδ,hmodels⟩ := of_decide_eq_true hc
  have hδ' : (p.left.delta:ℝ)≤(p.rootRadius:ℝ)/s := by exact_mod_cast hδ
  have hroot' := (hroot (p.time s x) ht.2.1).trans hδ'
  have hleft' := hleft (p.time s x) ht.2.1
  have hright' := hright (2-p.time s x) ht.2.2
  have hh : 2-(2-p.time s x)=p.time s x := by ring
  rw [hh] at hright'
  rw [← p.leftCoordinate_eval s x] at hroot'
  change |R.normalizedFilter hσ (p.time s x)-
    (Poly.exactPolynomial s p.left.p).eval (p.left.localCoordinate s (p.time s x))|≤_ at hleft'
  rw [← p.leftCoordinate_eval s x] at hleft'
  change |R.normalizedReflectedFilter hσ (p.time s x)-
    (Poly.exactPolynomial s p.right.p).eval (p.right.localCoordinate s (2-p.time s x))|≤_ at hright'
  rw [← p.rightCoordinate_eval hs x] at hright'
  intro i I hi
  rw [hmodels] at hi
  rcases i with _|i
  · have he : I=Poly.exactBounds [p.start,p.width] := by simpa [Panel.models] using hi.symm
    subst I
    simpa only [ContactExpr.values,p.time_eval] using (Poly.exactBounds_sound hs [p.start,p.width]).at x
  rcases i with _|i
  · have he : I=[piB] := by simpa [Panel.models] using hi.symm
    subst I
    simpa only [ContactExpr.values,eval_C] using
      (show Poly.Rep s [piB] (C Real.pi) by
        simpa using Poly.Rep.cons hpi (Poly.Rep.nil (s := s))).at x
  rcases i with _|i
  · have he : I=valueModel s p.left.z p.leftCoordinate p.rootRadius := by
      simpa [Panel.models] using hi.symm
    subst I
    exact valueModel_sound hs p.left.z p.leftCoordinate hroot'
  rcases i with _|i
  · have he : I=valueModel s p.left.p p.leftCoordinate eL := by
      simpa [Panel.models] using hi.symm
    subst I
    exact valueModel_sound hs p.left.p p.leftCoordinate hleft'
  rcases i with _|i
  · have he : I=valueModel s p.right.p (p.rightCoordinate s) eR := by
      simpa [Panel.models] using hi.symm
    subst I
    exact valueModel_sound hs p.right.p (p.rightCoordinate s) hright'
  rcases i with _|i
  · have he : I=Poly.exactBounds p.g := by simpa [Panel.models] using hi.symm
    subst I
    exact (Poly.exactBounds_sound hs p.g).at x
  · simp [Panel.models] at hi

end
end chebyshev2.Numerics.IntegerCertificate.ContactPolynomial
