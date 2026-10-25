import polyak.ModeLocking.TwoLag.TangencyData
import polyak.ModeLocking.TwoLag.ExactJets

/-! Proposition twolagtangency(b), including both endpoints and the second
jets, proved as a genuine equivalence for every degree. -/
noncomputable section
namespace polyak.ModeLocking.TwoLag
open General Levels Set

private theorem cos_equal_iff {x y : ℝ} (hx : x∈Icc 0 Real.pi) (hy : y∈Icc 0 Real.pi) :
    Real.cos x=Real.cos y ↔ x=y := ⟨Real.strictAntiOn_cos.injOn hx hy, congrArg Real.cos⟩

private theorem endpoint_pi_negative (q : Tuning) (K : ℕ) {a b : ℝ} (ha : 0<a) (hb : 0≤b) :
    extension q 0 K a b Real.pi<0 := by
  change extension q 0 K a b (frequencyPi : ℝ)<0
  rw [extension_eq_symbol]
  exact symbol_pi_neg q K ha hb

/-- Full source equivalence; the strict rational inequality at c=1 carries
exactly the original zero-frequency curvature condition. -/
theorem double_tangencies_iff (q : Tuning) {K : ℕ} (hK : 2≤K) {a b : ℝ}
    (ha : 0<a) (hb : 0<b) (u : Fin 2→Frequency)
    (hu : ∀i,0<(u i : ℝ) ∧ (u i : ℝ)<Real.pi) :
    LagTangencies q K a b u ↔ RationalTangencies q K (b/a) u := by
  have hKpos : 0<K := by omega
  have hKone : 1≤K := by omega
  have hr := div_pos hb ha
  constructor
  · intro H
    have hbound : ∀c∈Icc (-1 : ℝ) 1,q.Xi c≤Psi K (b/a) c := by
      intro c hc
      rcases eq_or_lt_of_le hc.1 with hc0|hc0
      · subst c
        rw [Psi_neg_one]
        exact q.Xi_neg_one_neg.le
      rcases eq_or_lt_of_le hc.2 with hc1|hc1
      · subst c
        exact ((endpoint_curvature_iff q hKone ha hb.le).mp H.endpoint_curv).le
      let ω : Frequency := ⟨Real.arccos c,Real.arccos_nonneg c,Real.arccos_le_pi c⟩
      have hω : 0<(ω : ℝ) ∧ (ω : ℝ)<Real.pi :=
        ⟨Real.arccos_pos.mpr hc1,Real.arccos_lt_pi.mpr hc0⟩
      have hh := (symbol_nonpos_iff q hKpos ha hb.le ω hω).mp (by
        rw [←extension_eq_symbol]
        exact H.nonpos ω ω.property)
      simpa only [show (ω : ℝ)=Real.arccos c from rfl,Real.cos_arccos hc.1 hc.2] using hh
    have hvalue (i : Fin 2) : q.Xi (Real.cos (u i : ℝ))=Psi K (b/a) (Real.cos (u i : ℝ)) := by
      apply (extension_zero_iff q hKpos ha hb.le (hu i)).mp
      exact (H.zero_set (u i) (u i).property).mpr (Or.inr ⟨i,rfl⟩)
    refine ⟨?_,hvalue,?_⟩
    · intro c hc hne
      rcases eq_or_lt_of_le hc.1 with hc0|hc0
      · subst c
        rw [Psi_neg_one]
        exact q.Xi_neg_one_neg
      rcases eq_or_lt_of_le hc.2 with hc1|hc1
      · subst c
        exact (endpoint_curvature_iff q hKone ha hb.le).mp H.endpoint_curv
      let x := Real.arccos c
      have hx : x∈Ioo 0 Real.pi := ⟨Real.arccos_pos.mpr hc1,Real.arccos_lt_pi.mpr hc0⟩
      have hstrict : extension q 0 K a b x<0 := by
        apply lt_of_le_of_ne (H.nonpos x ⟨hx.1.le,hx.2.le⟩)
        intro hz
        rcases (H.zero_set x ⟨hx.1.le,hx.2.le⟩).mp hz with h0|⟨i,hi⟩
        · exact hx.1.ne' h0
        · apply hne i
          rw [←hi]
          exact (Real.cos_arccos hc.1 hc.2).symm
      have hh := (extension_neg_iff q hKpos ha hb.le hx).mp hstrict
      simpa only [x,Real.cos_arccos hc.1 hc.2] using hh
    · intro i
      apply (contact_curvature_iff q hKpos ha hb.le (u i) (hu i) (hvalue i)
        (contact_slopes q K hr.le (cos_mem_open (hu i)) hbound (hvalue i))).mp
      exact H.support_curv i
  · intro H
    have hvalue (i : Fin 2) : extension q 0 K a b (u i)=0 :=
      (extension_zero_iff q hKpos ha hb.le (hu i)).mpr (H.value i)
    have hstrict (x : ℝ) (hx : x∈Icc 0 Real.pi) (hx0 : x≠0)
        (hne : ∀i,x≠(u i : ℝ)) : extension q 0 K a b x<0 := by
      rcases eq_or_lt_of_le hx.2 with hpi|hpi
      · subst x
        exact endpoint_pi_negative q K ha hb.le
      have hx' : x∈Ioo 0 Real.pi := ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0),hpi⟩
      apply (extension_neg_iff q hKpos ha hb.le hx').mpr
      apply H.strict (Real.cos x) ⟨Real.neg_one_le_cos x,Real.cos_le_one x⟩
      intro i heq
      exact hne i ((cos_equal_iff hx (u i).property).mp heq)
    refine ⟨?_,?_,?_,?_⟩
    · intro x hx
      by_cases h0 : x=0
      · subst x
        exact (extension_zero_endpoint q 0 K a b).le
      by_cases hs : ∃i,x=(u i : ℝ)
      · obtain ⟨i,rfl⟩ := hs
        exact (hvalue i).le
      · exact (hstrict x hx h0 (by simpa only [not_exists] using hs)).le
    · intro x hx
      constructor
      · intro hz
        by_cases h0 : x=0
        · exact Or.inl h0
        right
        by_contra hs
        exact (hstrict x hx h0 (by simpa only [not_exists] using hs)).ne hz
      · intro hz
        rcases hz with rfl|⟨i,rfl⟩
        · exact extension_zero_endpoint q 0 K a b
        · exact hvalue i
    · intro i
      apply (contact_curvature_iff q hKpos ha hb.le (u i) (hu i) (H.value i)
        (contact_slopes q K hr.le (cos_mem_open (hu i)) H.bound (H.value i))).mpr
      exact H.curvature i
    · apply (endpoint_curvature_iff q hKone ha hb.le).mpr
      exact H.strict 1 ⟨by norm_num,le_rfl⟩ (fun i=>(cos_mem_open (hu i)).2.ne')

end polyak.ModeLocking.TwoLag
