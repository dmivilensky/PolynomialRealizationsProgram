import polyak.General.Regions.Topology

/-! Article: Corollary C(a). A relative boundary point has an actual interior
double zero; vertex and discriminant formulas describe the tangency exactly. -/
namespace polyak.General.Regions
noncomputable section
open Filter Set
open scoped Topology

/-- Weak feasibility at an interior zero forces a double zero. -/
theorem L_derivative_zero_of_weak_zero (q : Tuning) (hq : WeakOmegaOne q)
    {c : ℝ} (hc : c∈Ioo (-1:ℝ) 1) (hz : q.L c=0) :
    8*q.beta*c+linearCoefficient q=0 := by
  have hmin : IsLocalMin q.L c := by
    filter_upwards [Ioo_mem_nhds hc.1 hc.2] with d hd
    rw [hz]
    exact hq d ⟨hd.1.le,hd.2.le⟩
  have hderiv : HasDerivAt q.L (8*q.beta*c+linearCoefficient q) c := by
    have hh := (((hasDerivAt_id c).pow 2).const_mul (4*q.beta)).add
      (((hasDerivAt_id c).const_mul (linearCoefficient q)).add_const (constantCoefficient q))
    convert hh using 1
    · funext d; dsimp [Tuning.L,linearCoefficient,constantCoefficient]; ring
    · dsimp; ring
  exact hmin.hasDerivAt_eq_zero hderiv

/-- Every relative boundary tuning has positive momentum and zero discriminant. -/
theorem frontier_omegaOne_tangent {q : Tuning}
    (hq : q∈frontier {p : Tuning | OmegaOne p}) :
    0<q.beta ∧ vertex q∈Ioo (-1:ℝ) 1 ∧
      q.L (vertex q)=0 ∧ discriminant q=0 := by
  obtain ⟨hw,c,hc,hz⟩ := frontier_omegaOne_has_zero hq
  have hder := L_derivative_zero_of_weak_zero q hw hc hz
  have hb : 0<q.beta := by
    by_contra hh
    have he : q.beta=0 := le_antisymm (le_of_not_gt hh) q.beta_nonneg
    have hl : linearCoefficient q=0 := by simpa only [he,mul_zero,zero_mul,zero_add] using hder
    have hn := q.L_one_pos
    rw [L_eq_quadratic q,he,mul_zero,hl] at hn
    rw [L_eq_quadratic q,he,mul_zero,hl] at hz
    dsimp [quadratic] at hz hn
    linarith
  have hv : vertex q=c := by
    unfold vertex
    apply (div_eq_iff (by positivity : 4*q.beta≠0)).mpr
    dsimp [linearCoefficient] at hder
    linarith
  refine ⟨hb,by rwa [hv],by rwa [hv],?_⟩
  rw [L_eq_quadratic q] at hz
  dsimp [quadratic] at hz
  have he : 4*(4*q.beta)*quadratic (4*q.beta) (linearCoefficient q) (constantCoefficient q) c=
      (8*q.beta*c+linearCoefficient q)^2-
        ((linearCoefficient q)^2-4*(4*q.beta)*constantCoefficient q) := by
    dsimp [quadratic]; ring
  rw [hder,zero_pow (by norm_num : 2≠0)] at he
  have hdisc : (linearCoefficient q)^2-4*(4*q.beta)*constantCoefficient q=0 := by
    dsimp [quadratic] at he
    nlinarith
  have hd : (linearCoefficient q)^2-4*(4*q.beta)*constantCoefficient q=4*discriminant q := by
    dsimp [linearCoefficient,constantCoefficient,discriminant]; ring
  linarith

end
end polyak.General.Regions
