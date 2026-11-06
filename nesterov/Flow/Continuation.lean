import Mathlib.Analysis.ODE.ExistUnique

/-!
Article: the global continuation argument in §3.
Use: a uniform local existence interval on a forward invariant set gives a
true solution on the whole nonnegative half-line in an arbitrary Banach space.
-/
namespace nesterov.Flow
noncomputable section
open Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def join (a : ℝ) (f g : ℝ→E) (t : ℝ) : E := if t≤a then f t else g t

theorem hasDerivAt_join {a : ℝ} {f g : ℝ→E} {v : E}
    (hf : HasDerivAt f v a) (hg : HasDerivAt g v a) (he : f a=g a) :
    HasDerivAt (join a f g) v a := by
  have hl : HasDerivWithinAt (join a f g) v (Iic a) a :=
    hf.hasDerivWithinAt.congr (fun t ht => by exact ite_eq_left (show t≤a from ht)) (by simp [join])
  have hr : HasDerivWithinAt (join a f g) v (Ioi a) a :=
    hg.hasDerivWithinAt.congr (fun t ht => by exact ite_eq_right (not_le.mpr (show a<t from ht)))
      (by simpa [join] using he)
  have hu : Iic a∪Ioi a=(univ : Set ℝ) := by ext t; simp only [mem_union,mem_Iic,mem_Ioi,mem_univ,iff_true]; exact le_or_gt t a
  simpa only [hu,hasDerivWithinAt_univ] using hl.union hr

structure PartialCurve (V : E→E) (S : Set E) (x₀ : E) (a : ℝ) (n : ℕ) where
  curve : ℝ→E
  initial : curve 0=x₀
  derivative : ∀ t,0≤t → t≤(n:ℝ)*a → HasDerivAt curve (V (curve t)) t
  invariant : ∀ t,0≤t → t≤(n:ℝ)*a → curve t∈S

variable {V : E→E} {S : Set E} {x₀ : E} {a : ℝ}

def PartialCurve.extend (ha : 0<a)
    (hloc : ∀ z∈S,∃ γ : ℝ→E,γ 0=z ∧
      (∀ t∈Icc 0 a,HasDerivAt γ (V (γ t)) t) ∧ ∀ t∈Icc 0 a,γ t∈S)
    {n : ℕ} (p : PartialCurve V S x₀ a n) : PartialCurve V S x₀ a (n+1) := by
  classical
  let H := hloc (p.curve ((n:ℝ)*a))
    (p.invariant _ (mul_nonneg (Nat.cast_nonneg _) ha.le) le_rfl)
  let γ := Classical.choose H
  have hγ0 := (Classical.choose_spec H).1
  have hγd := (Classical.choose_spec H).2.1
  have hγS := (Classical.choose_spec H).2.2
  let g := fun t => γ (t-(n:ℝ)*a)
  have he : p.curve ((n:ℝ)*a)=g ((n:ℝ)*a) := by
    change p.curve ((n:ℝ)*a)=γ (((n:ℝ)*a)-(n:ℝ)*a)
    simpa only [sub_self] using hγ0.symm
  have hgd (t : ℝ) (ht : t-(n:ℝ)*a∈Icc 0 a) : HasDerivAt g (V (g t)) t := by
    simpa only [g,γ,Function.comp_def,one_smul,id_eq] using
      (hγd _ ht).scomp t (hasDerivAt_id t |>.sub_const ((n:ℝ)*a))
  refine ⟨join ((n:ℝ)*a) p.curve g,?_,?_,?_⟩
  · simp [join,mul_nonneg (Nat.cast_nonneg n) ha.le,p.initial]
  · intro t ht0 ht
    rcases lt_trichotomy t ((n:ℝ)*a) with hlt | rfl | hgt
    · have hh := p.derivative t ht0 hlt.le
      have heq : join ((n:ℝ)*a) p.curve g =ᶠ[𝓝 t] p.curve := by
        filter_upwards [eventually_lt_nhds hlt] with s hs
        simp [join,hs.le]
      simpa [join,hlt.le] using hh.congr_of_eventuallyEq heq
    · simpa [join] using hasDerivAt_join
        (p.derivative _ ht0 le_rfl)
        (by simpa only [←he] using hgd ((n:ℝ)*a) (by simp [ha.le])) he
    · have hh := hgd t ⟨by linarith,by push_cast at ht; linarith⟩
      have heq : join ((n:ℝ)*a) p.curve g =ᶠ[𝓝 t] g := by
        filter_upwards [eventually_gt_nhds hgt] with s hs
        simp [join,not_le.mpr hs]
      simpa [join,not_le.mpr hgt] using hh.congr_of_eventuallyEq heq
  · intro t ht0 ht
    by_cases hle : t≤(n:ℝ)*a
    · simpa [join,hle] using p.invariant t ht0 hle
    · simp only [join,ite_eq_right hle,g]
      exact hγS _ ⟨by linarith,by push_cast at ht; linarith⟩

theorem PartialCurve.extend_eq (ha : 0<a)
    (hloc : ∀ z∈S,∃ γ : ℝ→E,γ 0=z ∧
      (∀ t∈Icc 0 a,HasDerivAt γ (V (γ t)) t) ∧ ∀ t∈Icc 0 a,γ t∈S)
    {n : ℕ} (p : PartialCurve V S x₀ a n) {t : ℝ} (ht : t≤(n:ℝ)*a) :
    (p.extend ha hloc).curve t=p.curve t := by
  unfold PartialCurve.extend
  simp only [join,ite_eq_left ht]

/-- Uniform local existence on a forward invariant set suffices for global
forward existence; no compactness of bounded sets is used. -/
theorem exists_forward_curve (ha : 0<a) (hx : x₀∈S)
    (hloc : ∀ z∈S,∃ γ : ℝ→E,γ 0=z ∧
      (∀ t∈Icc 0 a,HasDerivAt γ (V (γ t)) t) ∧ ∀ t∈Icc 0 a,γ t∈S) :
    ∃ γ : ℝ→E,γ 0=x₀ ∧ ∀ t,0≤t → HasDerivAt γ (V (γ t)) t ∧ γ t∈S := by
  classical
  obtain ⟨γ₀,h₀,hd₀,hS₀⟩ := hloc x₀ hx
  let p₀ : PartialCurve V S x₀ a 0 := ⟨γ₀,h₀,
    fun t ht hle => hd₀ t ⟨ht,by
      have hle' : t≤0 := by simpa using hle
      exact hle'.trans ha.le⟩,
    fun t ht hle => hS₀ t ⟨ht,by
      have hle' : t≤0 := by simpa using hle
      exact hle'.trans ha.le⟩⟩
  let p : (n : ℕ)→PartialCurve V S x₀ a n := fun n => Nat.rec p₀ (fun _ q => q.extend ha hloc) n
  have hstep (n : ℕ) {t : ℝ} (ht : t≤(n:ℝ)*a) : (p (n+1)).curve t=(p n).curve t :=
    PartialCurve.extend_eq ha hloc (p n) ht
  have hmono {n m : ℕ} (hnm : n≤m) {t : ℝ} (ht : t≤(n:ℝ)*a) :
      (p m).curve t=(p n).curve t := by
    induction m,hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih =>
      rw [hstep m (ht.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hnm) ha.le)),ih]
  let index (t : ℝ) := Nat.ceil (t/a)+1
  have hcover (t : ℝ) : t<(index t:ℝ)*a := by
    have hh := Nat.le_ceil (t/a)
    have hh' : t/a<(index t:ℝ) := by dsimp [index]; push_cast; linarith
    exact (div_lt_iff₀ ha).mp hh'
  let γ := fun t => (p (index t)).curve t
  have heq (n : ℕ) {t : ℝ} (ht : t≤(n:ℝ)*a) : γ t=(p n).curve t := by
    dsimp [γ]
    rcases le_total n (index t) with hni | hin
    · exact hmono hni ht
    · exact (hmono hin (hcover t).le).symm
  refine ⟨γ,?_,fun t ht => ?_⟩
  · rw [heq 0 (by simp),(p 0).initial]
  · let n := index t
    have ht' : t<(n:ℝ)*a := hcover t
    have hγeq : γ =ᶠ[𝓝 t] (p n).curve := by
      filter_upwards [eventually_lt_nhds ht'] with s hs
      exact heq n hs.le
    rw [heq n ht'.le]
    exact ⟨((p n).derivative t ht ht'.le).congr_of_eventuallyEq hγeq,
      (p n).invariant t ht ht'.le⟩

end
end nesterov.Flow
