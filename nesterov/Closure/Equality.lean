import nesterov.Closure.SpectralSet
import nesterov.IQC.StateMass
import nesterov.Duality.Separation

/-!
Theorem A(a–d), closure of the exact division-free spectral program against the
actual uniform all-Hilbert rate. The upper bound is the one-exponent IQC
argument, while every feasible point is realized by an actual single potential.
-/
namespace nesterov.Closure
noncomputable section
open Spectral
open nesterov.IQC
variable (M : StationaryMethod)

/-- Every exponent strictly above the maximal feasible one has an actual
finite strict certificate, with no stability hypothesis on the method. -/
theorem certificate_above_T {μ L t : ℝ} (hμ : 0<μ) (hμL : μ<L) (ht : T M μ L<t) :
    Nonempty (Duality.StrictCertificate (M.symbolPair μ L t) t) := by
  apply (Duality.infeasible_iff_strictCertificate _ _).mp
  rintro ⟨ν,C,hf⟩
  have hh:=(T_isGreatest M hμ hμL).2 (show t∈spectralSet M μ L from ⟨ν,C,hf⟩)
  linarith

/-- The middle-quadratic recursion is stable at every exponent above T. -/
theorem middleRadius_lt_exp_of_T_lt {μ L t : ℝ} (hμ : 0<μ) (hμL : μ<L) (ht : T M μ L<t) :
    middleRadius M μ L<Real.exp t := by
  have hq:=(Rates.quadraticRate_pos M hμ hμL)
  have hl:=Real.exp_le_exp.mpr (log_quadraticRate_le_T M hμ hμL)
  rw [Real.exp_log hq] at hl
  exact (middleRadius_le_quadraticRate M hμ hμL).trans_lt
    (hl.trans_lt (Real.exp_lt_exp.mpr ht))

/-- The maximal feasible exponent is exactly the true uniform asymptotic
exponent, with the original supremum over all objectives and Hilbert spaces. -/
theorem exponent_eq_T {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) :
    Rates.exponent M μ L=T M μ L := by
  apply le_antisymm
  · by_contra! h
    let t:=(T M μ L+Rates.exponent M μ L)/2
    have ht : T M μ L<t:=by dsimp [t]; linarith
    have he : t<Rates.exponent M μ L:=by dsimp [t]; linarith
    obtain ⟨cert⟩:=certificate_above_T M hμ hμL ht
    have hr:=one_exponent hμ hμL (middleRadius_lt_exp_of_T_lt M hμ hμL ht) cert
    have hh:=Real.exp_lt_exp.mp hr
    exact (not_lt_of_ge he.le) hh
  · exact spectralSet_le_exponent M hμ hμL (T_isGreatest M hμ hμL).1

/-- Theorem A(b): the spectral maximum equals the actual uniform rate. -/
theorem rate_eq_exp_T {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L) :
    Rates.rate M μ L=Real.exp (T M μ L) := by
  rw [Rates.rate,exponent_eq_T M hμ hμL]

/-- Every feasible spectrum excludes every strict certificate at that exponent. -/
theorem no_certificate_of_feasible {μ L t : ℝ} {ν : Spectrum} {C : ℝ}
    (hf : Feasible (M.symbolPair μ L t) t ν C) :
    IsEmpty (Duality.StrictCertificate (M.symbolPair μ L t) t) := by
  refine ⟨fun cert=>cert.not_feasible ν C hf⟩

/-- Theorem A(c), the exact interval above the middle-quadratic root radius.
The exponential form also covers r_c=0 without assigning a finite log(0). -/
theorem feasible_above_middle_iff {μ L t : ℝ} (hμ : 0<μ) (hμL : μ<L)
    (ht : middleRadius M μ L<Real.exp t) :
    (∃ ν C,Feasible (M.symbolPair μ L t) t ν C) ↔ t≤T M μ L := by
  constructor
  · exact fun hf=>(T_isGreatest M hμ hμL).2 hf
  · intro htT
    by_contra hn
    obtain ⟨cert⟩:=(Duality.infeasible_iff_strictCertificate _ _).mp hn
    have hr:=one_exponent hμ hμL ht cert
    rw [rate_eq_exp_T M hμ hμL] at hr
    have hh:=Real.exp_lt_exp.mp hr
    linarith

/-- The literal logarithmic interval when the middle radius is positive. -/
theorem spectralSet_above_log_middle {μ L : ℝ} (hμ : 0<μ) (hμL : μ<L)
    (hc : 0<middleRadius M μ L) :
    spectralSet M μ L∩Set.Ioi (Real.log (middleRadius M μ L))=
      Set.Ioc (Real.log (middleRadius M μ L)) (T M μ L) := by
  ext t
  constructor
  · rintro ⟨hf,ht⟩
    exact ⟨ht,(T_isGreatest M hμ hμL).2 hf⟩
  · rintro ⟨ht,hT⟩
    have he:=Real.exp_lt_exp.mpr ht
    rw [Real.exp_log hc] at he
    exact ⟨(feasible_above_middle_iff M hμ hμL he).mpr hT,ht⟩

/-- On the stable side of r_c the finite certificate is exactly equivalent
to a strict bound on the actual rate. -/
theorem certificate_iff_rate_lt {μ L t : ℝ} (hμ : 0<μ) (hμL : μ<L)
    (ht : middleRadius M μ L<Real.exp t) :
    Nonempty (Duality.StrictCertificate (M.symbolPair μ L t) t) ↔
      Rates.rate M μ L<Real.exp t := by
  constructor
  · rintro ⟨cert⟩
    exact one_exponent hμ hμL ht cert
  · intro hr
    rw [rate_eq_exp_T M hμ hμL] at hr
    exact certificate_above_T M hμ hμL (Real.exp_lt_exp.mp hr)

end
end nesterov.Closure
