import jacobi.Bessel.SturmZeros

/-!
Article: jacobi, Proposition B.1.
The singular first-interval comparison and ordinary nodal comparisons
are assembled into a finite-prefix theorem for actual ordered zero lists.
This is the shared counting step for both directions of the Jacobi/Bessel
comparison; its hypotheses describe the original ODEs and genuine zero lists.
Use: compares the true Jacobi and Bessel zeros in both directions, retaining their canonical source numbering at the singular endpoint.
-/
namespace jacobi.Bessel
noncomputable section
open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Strictly ordered restoring coefficients order every numbered zero in a prescribed actual finite nodal prefix.
Use: compares the true Jacobi and Bessel zeros in both directions, retaining their canonical source numbering at the singular endpoint.
Article: jacobi, Proposition B.1.
Source: the classical singular Sturm comparison theorem, assembled here from proved Wronskian and intermediate-value arguments.
Proof: initial positivity and the actual zero-free first nodal interval
fix the first original branch. Singular comparison supplies a genuine
comparator zero before its first zero, and true first-zero minimality
bounds the first comparator index. On each later genuine nodal interval,
ordinary Sturm comparison supplies another zero beyond the previously
bounded comparator zero. Actual successor minimality advances the index. -/
theorem numbered_sturm_comparison {f f' f'' g g' g'' q0 q1 : ℝ → ℝ}
    {R : ℝ} (K : ℕ) (leftZeros rightZeros : ℕ → ℝ)
    (hf : ∀ x∈Ioc 0 R,HasDerivAt f (f' x) x)
    (hf' : ∀ x∈Ioc 0 R,HasDerivAt f' (f'' x) x)
    (hg : ∀ x∈Ioc 0 R,HasDerivAt g (g' x) x)
    (hg' : ∀ x∈Ioc 0 R,HasDerivAt g' (g'' x) x)
    (he0 : ∀ x∈Ioo 0 R,f'' x+q0 x*f x=0)
    (he1 : ∀ x∈Ioo 0 R,g'' x+q1 x*g x=0)
    (hq : ∀ x∈Ioo 0 R,q0 x<q1 x)
    (hlim : Tendsto (fun x => f' x*g x-f x*g' x) (𝓝[>] 0) (𝓝 0))
    (hinitF : ∀ᶠ x in 𝓝[>] (0:ℝ),0<f x)
    (hinitG : ∀ᶠ x in 𝓝[>] (0:ℝ),0<g x)
    (hA : ∀ m≤K,0<leftZeros m ∧ leftZeros m≤R)
    (hAmono : ∀ m<K,leftZeros m<leftZeros (m+1))
    (hAzero : ∀ m≤K,f (leftZeros m)=0)
    (hAfirst : ∀ x∈Ioo 0 (leftZeros 0),f x≠0)
    (hAgap : ∀ m<K,∀ x∈Ioo (leftZeros m) (leftZeros (m+1)),f x≠0)
    (hBfirst : ∀ x∈Ioc 0 R,g x=0 → rightZeros 0≤x)
    (hBsucc : ∀ m<K,∀ x∈Ioc 0 R,g x=0 → rightZeros m<x → rightZeros (m+1)≤x) :
    ∀ m≤K,rightZeros m<leftZeros m := by
  -- A new actual comparator zero is obtained on each disjoint original nodal interval, so no zero can be counted twice.
  intro m
  induction m with
  | zero =>
    intro _
    have hA0 := hA 0 (Nat.zero_le K)
    have hioc : Ioc 0 (leftZeros 0)⊆Ioc 0 R := fun _ hx => ⟨hx.1,hx.2.trans hA0.2⟩
    have hioo : Ioo 0 (leftZeros 0)⊆Ioo 0 R := fun _ hx => ⟨hx.1,hx.2.trans_le hA0.2⟩
    have hpoint : ∀ᶠ x in 𝓝[>] (0:ℝ),x∈Ioo 0 (leftZeros 0) ∧ 0<f x :=
      Filter.Eventually.and (Ioo_mem_nhdsGT hA0.1) hinitF
    obtain ⟨t,ht,hpt⟩ := hpoint.exists
    have hpos := positive_on_interval_of_no_zero
      (fun x hx => (hf x (hioc ⟨hx.1,hx.2.le⟩)).continuousAt.continuousWithinAt)
      hAfirst ht hpt
    obtain ⟨x,hx,hzx⟩ := singular_sturm_zero hA0.1
      (fun x hx => hf x (hioc hx)) (fun x hx => hf' x (hioc hx))
      (fun x hx => hg x (hioc hx)) (fun x hx => hg' x (hioc hx))
      (fun x hx => he0 x (hioo hx)) (fun x hx => he1 x (hioo hx))
      (fun x hx => hq x (hioo hx)) hlim (hAzero 0 (Nat.zero_le K)) hpos hinitG
    exact (hBfirst x ⟨hx.1,hx.2.le.trans hA0.2⟩ hzx).trans_lt hx.2
  | succ m ih =>
    intro hm
    have hmK : m<K := by omega
    have hAm := hA m hmK.le
    have hAn := hA (m+1) hm
    have hioc : Icc (leftZeros m) (leftZeros (m+1))⊆Ioc 0 R :=
      fun _ hx => ⟨hAm.1.trans_le hx.1,hx.2.trans hAn.2⟩
    have hioo : Ioo (leftZeros m) (leftZeros (m+1))⊆Ioo 0 R :=
      fun _ hx => ⟨hAm.1.trans hx.1,hx.2.trans_le hAn.2⟩
    obtain ⟨x,hx,hzx⟩ := sturm_zero_between (hAmono m hmK)
      (fun x hx => hf x (hioc hx)) (fun x hx => hf' x (hioc hx))
      (fun x hx => hg x (hioc hx)) (fun x hx => hg' x (hioc hx))
      (fun x hx => he0 x (hioo hx)) (fun x hx => he1 x (hioo hx))
      (fun x hx => hq x (hioo hx)) (hAzero m hmK.le) (hAzero (m+1) hm) (hAgap m hmK)
    exact (hBsucc m hmK x ⟨hAm.1.trans hx.1,hx.2.le.trans hAn.2⟩ hzx
      ((ih hmK.le).trans hx.1)).trans_lt hx.2

end
end jacobi.Bessel
