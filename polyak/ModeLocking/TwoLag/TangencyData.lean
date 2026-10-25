import polyak.ModeLocking.TwoLag.ContactExtension

/-! The two equivalent primary formulations of double tangency. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open General Levels Set

structure LagTangencies (q : Tuning) (K : ℕ) (a b : ℝ) (u : Fin 2→Frequency) : Prop where
  nonpos : ∀x∈Icc 0 Real.pi,extension q 0 K a b x≤0
  zero_set : ∀x∈Icc 0 Real.pi,extension q 0 K a b x=0 ↔ x=0 ∨ ∃i,x=(u i : ℝ)
  support_curv : ∀i,deriv^[2] (extension q 0 K a b) (u i : ℝ)<0
  endpoint_curv : deriv^[2] (extension q 0 K a b) 0<0

structure RationalTangencies (q : Tuning) (K : ℕ) (r : ℝ) (u : Fin 2→Frequency) : Prop where
  strict : ∀c∈Icc (-1 : ℝ) 1,(∀i,c≠Real.cos (u i : ℝ))→q.Xi c<Psi K r c
  value : ∀i,q.Xi (Real.cos (u i : ℝ))=Psi K r (Real.cos (u i : ℝ))
  curvature : ∀i,0<deriv^[2] (fun c=>Psi K r c-q.Xi c) (Real.cos (u i : ℝ))

theorem cos_mem_open {x : ℝ} (hx : x∈Ioo 0 Real.pi) : Real.cos x∈Ioo (-1 : ℝ) 1 := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  constructor <;> nlinarith [Real.sin_sq_add_cos_sq x, sq_pos_of_pos hs,
    Real.neg_one_le_cos x, Real.cos_le_one x]

theorem extension_eq_symbol (q : Tuning) (K : ℕ) (a b : ℝ) (ω : Frequency) :
    extension q 0 K a b ω=symbol q K a b ω := by
  rw [extension_actual,Geometry.shiftedCurve_zero]
  rfl

theorem extension_neg_iff (q : Tuning) {K : ℕ} (hK : 0<K) {a b x : ℝ}
    (ha : 0<a) (hb : 0≤b) (hx : x∈Ioo 0 Real.pi) :
    (extension q 0 K a b x<0 ↔ q.Xi (Real.cos x)<Psi K (b/a) (Real.cos x)) := by
  let ω : Frequency := ⟨x,hx.1.le,hx.2.le⟩
  change (extension q 0 K a b ω<0 ↔ _)
  rw [extension_eq_symbol]
  exact symbol_neg_iff q hK ha hb ω hx

theorem extension_zero_iff (q : Tuning) {K : ℕ} (hK : 0<K) {a b x : ℝ}
    (ha : 0<a) (hb : 0≤b) (hx : x∈Ioo 0 Real.pi) :
    (extension q 0 K a b x=0 ↔ q.Xi (Real.cos x)=Psi K (b/a) (Real.cos x)) := by
  let ω : Frequency := ⟨x,hx.1.le,hx.2.le⟩
  change (extension q 0 K a b ω=0 ↔ _)
  rw [extension_eq_symbol]
  exact symbol_zero_iff q hK ha hb ω hx

namespace RationalTangencies
variable {q : Tuning} {K : ℕ} {r : ℝ} {u : Fin 2→Frequency} (H : RationalTangencies q K r u)

include H in
theorem bound (c : ℝ) (hc : c∈Icc (-1 : ℝ) 1) : q.Xi c≤Psi K r c := by
  by_cases heq : ∃i,c=Real.cos (u i : ℝ)
  · obtain ⟨i,rfl⟩ := heq
    exact (H.value i).le
  · exact (H.strict c hc (by simpa only [not_exists] using heq)).le

end RationalTangencies

end polyak.ModeLocking.TwoLag
