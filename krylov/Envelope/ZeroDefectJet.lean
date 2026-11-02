import krylov.Envelope.FirstJets
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, genuine zero-reference operator-defect product jets.
Use: eliminate actual coefficient and step derivative terms from true virtual injection and unevaluated output defect actions at the original quadratic reference.
Source: genuine continuous-linear evaluation and scalar-vector product rules, with the actual zero reference operator defect.
-/

namespace krylov.Envelope
noncomputable section
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

/-- A genuine zero-reference operator-defect weighted action has only the actual reference-weighted primitive operator derivative in its true first jet.
Use: A genuine zero-reference operator-defect weighted action has only the actual reference-weighted primitive operator derivative in its true first jet.
Article: main_krylov, thm:E1, genuine zero-reference operator-defect product jets.
Proof: Differentiate the real operator action and scalar product; both actual vanishing reference factors remove their corresponding coefficient and vector derivative terms. -/
theorem weighted_zero_defect_jet (C : ι → ℝ → E →L[ℝ] E) (s : ι → ℝ → E)
    (w : ι → ℝ → ℝ) (dC : ι → E →L[ℝ] E) (ds : ι → E) (dw : ι → ℝ)
    (hC : ∀ i,HasDerivAt (C i) (dC i) 0) (hs : ∀ i,HasDerivAt (s i) (ds i) 0)
    (hw : ∀ i,HasDerivAt (w i) (dw i) 0) (h0 : ∀ i,C i 0=0) :
    HasDerivAt (fun t => ∑ i,w i t • C i t (s i t)) (∑ i,w i 0 • dC i (s i 0)) 0 := by
  -- The actual vanishing reference operator removes the true moving-vector and scalar-coefficient derivative terms.
  have hact (i : ι) : HasDerivAt (fun t => C i t (s i t)) (dC i (s i 0)) 0 := by
    simpa only [h0,_root_.zero_apply,zero_add] using operator_jet_action (C i) (s i) (dC i) (ds i) 0 (hC i) (hs i)
  have h := HasDerivAt.sum (fun i (_ : i∈(Finset.univ : Finset ι)) => (hw i).smul (hact i))
  have hh : HasDerivAt (∑ i,w i • (fun t => C i t (s i t))) (∑ i,w i 0 • dC i (s i 0)) 0 := by
    simpa only [h0,_root_.zero_apply,smul_zero,add_zero] using h
  convert hh using 1
  funext t
  simp only [Finset.sum_apply,Pi.smul_apply']
end
end krylov.Envelope
