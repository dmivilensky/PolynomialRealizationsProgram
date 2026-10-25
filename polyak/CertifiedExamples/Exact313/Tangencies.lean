import polyak.CertifiedExamples.Exact313.ContactPolynomial
import polyak.CertifiedExamples.Exact313.ContactJets
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Complete global E1: no frequency mesh is used. The exact quintic
factorization gives the strict sign and both nondegenerate double contacts. -/
noncomputable section
namespace polyak.CertifiedExamples.Exact313
open General Levels ModeLocking.TwoLag Set Filter
open scoped Topology

theorem rational_difference {c : ℝ} (hc : c∈Icc (-1:ℝ) 1) :
    Psi 4 rStar c-CStar.eval c= -contactPolynomial c/denominator rStar c := by
  rw [psi_four,contactPolynomial_identity]
  field_simp [(denominator_pos scalarRoot_positive.le hc).ne']
  ring

theorem rational_strict {c : ℝ} (hc : c∈Icc (-1:ℝ) 1) (h₁ : c≠c₁) (h₂ : c≠c₂) :
    CStar.eval c<Psi 4 rStar c := by
  apply sub_pos.mp
  rw [rational_difference hc]
  exact div_pos (neg_pos.mpr (contactPolynomial_negative hc.1 h₁ h₂))
    (denominator_pos scalarRoot_positive.le hc)

theorem rational_curvature {a b : ℝ} (ha : a∈Ioo (-1:ℝ) 1) (hab : a≠b)
    (hfactor : ∀c,contactPolynomial c=(c-a)^2*(c-b)^2*contactLine c) :
    0<deriv^[2] (fun c=>Psi 4 rStar c-CStar.eval c) a := by
  let H : ℝ→ℝ := fun c=>(c-b)^2*(-contactLine c)/denominator rStar c
  have hd := (denominator_pos scalarRoot_positive.le ⟨ha.1.le,ha.2.le⟩).ne'
  have hH : ContDiffAt ℝ 2 H a := by
    dsimp [H,contactLine,denominator]
    fun_prop (disch := exact hd)
  have hpos : 0<H a := div_pos
    (mul_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hab))
      (neg_pos.mpr (contactLine_negative ha.1.le)))
    (denominator_pos scalarRoot_positive.le ⟨ha.1.le,ha.2.le⟩)
  have he : (fun c=>Psi 4 rStar c-CStar.eval c) =ᶠ[𝓝 a] (fun c=>(c-a)^2*H c) := by
    filter_upwards [Ioo_mem_nhds ha.1 ha.2] with c hc
    rw [rational_difference ⟨hc.1.le,hc.2.le⟩,hfactor]
    dsimp [H]
    ring
  have he2 : deriv^[2] (fun c=>Psi 4 rStar c-CStar.eval c) a=
      deriv^[2] (fun c=>(c-a)^2*H c) a := by
    simpa only [iteratedDeriv_eq_iterate] using he.iteratedDeriv_eq 2
  rw [he2,second_square_factor hH]
  positivity

theorem rationalTangencies : RationalTangencies qStar 4 rStar atoms := by
  refine ⟨?_,contact_values,?_⟩
  · intro c hc hne
    rw [qStar_Xi]
    apply rational_strict hc
    · simpa only [atoms_cos,ite_true] using hne 0
    · simpa only [atoms_cos,show (1:Fin 2)≠0 by decide,ite_false] using hne 1
  · intro i
    have he : (fun c=>Psi 4 rStar c-qStar.Xi c)=(fun c=>Psi 4 rStar c-CStar.eval c) := by
      funext c
      rw [qStar_Xi]
    rw [he,atoms_cos]
    fin_cases i
    · apply rational_curvature c₁_mem c₁_lt_c₂.ne
      intro c
      exact contactPolynomial_factor c
    · apply rational_curvature c₂_mem c₁_lt_c₂.ne.symm
      intro c
      rw [contactPolynomial_factor]
      dsimp [contactLine]
      ring

theorem lagTangencies : LagTangencies qStar 4 (1/(1+rStar)) (rStar/(1+rStar)) atoms := by
  have hr : 0<1+rStar := by linarith [scalarRoot_positive]
  have ha : 0<1/(1+rStar) := one_div_pos.mpr hr
  have hb : 0<rStar/(1+rStar) := div_pos scalarRoot_positive hr
  apply (double_tangencies_iff qStar (by norm_num : 2≤4) ha hb atoms atoms_interior).mpr
  have he : (rStar/(1+rStar))/(1/(1+rStar))=rStar := by field_simp
  rw [he]
  exact rationalTangencies

end polyak.CertifiedExamples.Exact313
