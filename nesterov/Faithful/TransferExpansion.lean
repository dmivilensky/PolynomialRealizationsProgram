import nesterov.Faithful.Low

/-! The literal rational Taylor expansion defining the effective phase lead.
The remainder is complex analytic at z=1; no stability or coprimality is needed. -/
namespace nesterov.Faithful
noncomputable section
open Polynomial

/-- The normalized quotient has the source first-order Taylor polynomial and
an analytic quadratic remainder. The equality is global; only analyticity of
the remainder is local, so polynomial zeros away from 1 need no exclusions. -/
theorem normalized_transfer_expansion (u q : Polynomial ℝ) {y : ℝ} (hy : y≠0)
    (hu : u.eval 1=1) (hq : q.eval 1= -1/y) :
    ∃ R : ℂ→ℂ,AnalyticAt ℂ R 1 ∧ ∀ z : ℂ,
      -(y:ℂ)*evalComplex q z/evalComplex u z=
        1-(1+(effectiveLead u q y:ℂ))*(z-1)+(z-1)^2*R z := by
  let f : ℂ→ℂ := fun w=> -(y:ℂ)*evalComplex q (1+w)/evalComplex u (1+w)
  have hu1 : evalComplex u 1=1 := by simp [hu]
  have hq1 : evalComplex q 1= -(1:ℂ)/(y:ℂ) := by simp [hq]
  have hyc : (y:ℂ)≠0 := by exact_mod_cast hy
  have heval (p : Polynomial ℝ) :
      AnalyticAt ℂ (fun w : ℂ=>evalComplex p (1+w)) 0 := by
    have hp : AnalyticAt ℂ (evalComplex p) (1+(0:ℂ)) := by
      unfold evalComplex
      exact (p.map Complex.ofRealHom).differentiable.analyticAt _
    exact hp.fun_comp (f:=fun w : ℂ=>1+w) (by fun_prop)
  have hder (p : Polynomial ℝ) :
      HasDerivAt (fun w : ℂ=>evalComplex p (1+w))
        ((p.derivative.eval 1:ℝ):ℂ) 0 := by
    have hg : HasDerivAt (fun w : ℂ=>1+w) 1 0 := by
      simpa only [id_eq] using (hasDerivAt_id (0:ℂ)).const_add (1:ℂ)
    have hh := ((p.map Complex.ofRealHom).hasDerivAt (1+(0:ℂ))).comp 0 hg
    simpa [evalComplex,Function.comp_def,Polynomial.derivative_map] using hh
  have hf : AnalyticAt ℂ f 0 :=
    (analyticAt_const.fun_mul (heval q)).div (heval u) (by simp [hu1])
  have hf0 : f 0=1 := by
    simp only [f,add_zero,hu1,hq1,div_one]
    field_simp
  have hd : HasDerivAt f (-(1+(effectiveLead u q y:ℂ))) 0 := by
    have hh := ((hder q).const_mul (-(y:ℂ))).div (hder u) (by simp [hu1])
    convert hh using 1
    simp only [add_zero,hu1,hq1,one_pow,div_one,mul_one]
    unfold effectiveLead
    push_cast
    field_simp
    ring
  obtain ⟨S,hS,he⟩ := hf.exists_eq_sum_add_pow_mul 2
  have hexp (w : ℂ) : f w=1-(1+(effectiveLead u q y:ℂ))*w+w^2*S w := by
    have hh := he w
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,iteratedDeriv_zero,
      iteratedDeriv_succ,Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,pow_zero,pow_one,
      zero_add,div_one,hd.deriv,hf0,smul_eq_mul] at hh
    convert hh using 1
    ring
  refine ⟨fun z=>S (z-1),?_,fun z=>?_⟩
  · have hz : AnalyticAt ℂ (fun z : ℂ=>z-1) 1 := by fun_prop
    have hs : AnalyticAt ℂ S ((1:ℂ)-1) := by simpa only [sub_self] using hS
    exact hs.fun_comp (f:=fun z : ℂ=>z-1) hz
  · have hh := hexp (z-1)
    simpa only [f,add_sub_cancel] using hh

/-- The unnumbered transfer-function expansion in Section 5, with its literal
factor -(z-1)^2 and a complex analytic O((z-1)^2) remainder in brackets. -/
theorem transfer_quotient_expansion (u q : Polynomial ℝ) {y : ℝ} (hy : y≠0)
    (hu : u.eval 1=1) (hq : q.eval 1= -1/y) :
    ∃ R : ℂ→ℂ,AnalyticAt ℂ R 1 ∧ ∀ z : ℂ,
      (y:ℂ)*evalComplex ((X-C 1)^2*q) z/evalComplex u z=
        -(z-1)^2*(1-(1+(effectiveLead u q y:ℂ))*(z-1)+(z-1)^2*R z) := by
  obtain ⟨R,hR,he⟩ := normalized_transfer_expansion u q hy hu hq
  refine ⟨R,hR,fun z=>?_⟩
  rw [←he z]
  simp [evalComplex]
  ring

end
end nesterov.Faithful
