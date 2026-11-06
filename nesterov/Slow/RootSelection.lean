import nesterov.Slow.RootPerturbation
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.FieldDivision

/-! Root selection and continuous deflation for bounded-degree complex polynomials.
These statements allow the leading coefficient to vanish at the limit. -/
namespace nesterov.Slow
noncomputable section
open Polynomial Filter Set
open scoped Topology

private lemma exists_closest_root (p : Polynomial ℂ) (z : ℂ)
    (h : ∃ r : ℂ,p.eval r=0) :
    ∃ r : ℂ,p.eval r=0 ∧ ∀ s : ℂ,p.eval s=0 → ‖r-z‖≤‖s-z‖ := by
  by_cases hp : p=0
  · subst p
    exact ⟨z,by simp,by intro s _;simp⟩
  · obtain ⟨s,hs⟩ := h
    have hne : p.roots.toFinset.Nonempty := ⟨s,by simpa using (mem_roots hp).mpr hs⟩
    obtain ⟨r,hr,hmin⟩ := p.roots.toFinset.exists_min_image (fun r=>‖r-z‖) hne
    refine ⟨r,(mem_roots hp).mp (by simpa using hr),?_⟩
    intro t ht
    exact hmin t (by simpa using (mem_roots hp).mpr ht)

/-- A selected actual root converges to any prescribed root of a nonzero limit. -/
theorem exists_root_selection {A : Type*} {l : Filter A}
    {p : A→Polynomial ℂ} {p₀ : Polynomial ℂ} {N : ℕ}
    (hdeg : ∀ a,(p a).natDegree≤N)
    (heval : ∀ z : ℂ,Tendsto (fun a=>(p a).eval z) l (𝓝 (p₀.eval z)))
    (hp₀ : p₀≠0) {z : ℂ} (hz : p₀.eval z=0) :
    ∃ r : A→ℂ,Tendsto r l (𝓝 z) ∧ ∀ᶠ a in l,(p a).eval (r a)=0 := by
  classical
  have hex (a : A) : ∃ r : ℂ,(∃ s : ℂ,(p a).eval s=0) →
      (p a).eval r=0 ∧ ∀ s : ℂ,(p a).eval s=0 → ‖r-z‖≤‖s-z‖ := by
    by_cases h : ∃ s : ℂ,(p a).eval s=0
    · obtain ⟨r,hr⟩ := exists_closest_root (p a) z h
      exact ⟨r,fun _=>hr⟩
    · exact ⟨z,fun hh=>False.elim (h hh)⟩
  choose r hr using hex
  refine ⟨r,?_,?_⟩
  · apply Metric.tendsto_nhds.mpr
    intro δ hδ
    filter_upwards [eventually_exists_root_near hdeg heval hp₀ hz hδ] with a ha
    obtain ⟨s,hs,hd⟩ := ha
    simpa only [dist_eq_norm] using (hr a ⟨s,hs⟩).2 s hs |>.trans_lt hd
  · filter_upwards [eventually_exists_root_near hdeg heval hp₀ hz (by norm_num : (0:ℝ)<1)] with a ha
    obtain ⟨s,hs,_⟩ := ha
    exact (hr a ⟨s,hs⟩).1

/-- Evaluations at finitely many fixed nodes recover every bounded-degree coefficient. -/
theorem tendsto_coeff_of_eval {A : Type*} {l : Filter A}
    {p : A→Polynomial ℂ} {p₀ : Polynomial ℂ} {N : ℕ}
    (hdeg : ∀ a,(p a).natDegree≤N) (hdeg₀ : p₀.natDegree≤N)
    (heval : ∀ z : ℂ,Tendsto (fun a=>(p a).eval z) l (𝓝 (p₀.eval z))) (n : ℕ) :
    Tendsto (fun a=>(p a).coeff n) l (𝓝 (p₀.coeff n)) := by
  classical
  let v : Fin (N+1)→ℂ := fun i=>(i.val:ℂ)
  have hv : Set.InjOn v (↑(Finset.univ : Finset (Fin (N+1))) : Set (Fin (N+1))) := by
    intro a _ b _ h
    apply Fin.ext
    change (a.val:ℂ)=(b.val:ℂ) at h
    exact_mod_cast h
  have hf (q : Polynomial ℂ) (hq : q.natDegree≤N) :
      q.coeff n=∑ i : Fin (N+1),q.eval (v i)*(Lagrange.basis Finset.univ v i).coeff n := by
    have hd : q.degree<(Finset.univ : Finset (Fin (N+1))).card := by
      simp only [Finset.card_univ,Fintype.card_fin]
      exact degree_le_natDegree.trans_lt (by exact_mod_cast (hq.trans_lt (Nat.lt_succ_self N)))
    have hh := congrArg (fun q : Polynomial ℂ=>q.coeff n) (Lagrange.eq_interpolate hv hd)
    simpa only [Lagrange.interpolate_apply,finsetSum_coeff,coeff_C_mul] using hh
  simp_rw [hf (p _) (hdeg _),hf p₀ hdeg₀]
  exact tendsto_finsetSum _ (fun i _=>(heval (v i)).mul_const _)

lemma complex_coeff_divByMonic_bounded (p : Polynomial ℂ) (a : ℂ) {N : ℕ}
    (hN : p.natDegree≤N) (n : ℕ) :
    (p /ₘ (X-C a)).coeff n=∑ i∈Finset.Icc (n+1) N,a^(i-(n+1))*p.coeff i := by
  rw [coeff_divByMonic_X_sub_C]
  apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hN)
  intro i hi hnot
  have hgt : p.natDegree < i := by
    have hlo := (Finset.mem_Icc.mp hi).1
    exact lt_of_not_ge (fun hh=>hnot (Finset.mem_Icc.mpr ⟨hlo,hh⟩))
  rw [coeff_eq_zero_of_natDegree_lt hgt,mul_zero]

theorem complex_tendsto_divByMonic_coeff {A : Type*} {l : Filter A}
    {p : A→Polynomial ℂ} {p₀ : Polynomial ℂ} {a : A→ℂ} {a₀ : ℂ} {N : ℕ}
    (hp : ∀ j,Tendsto (fun e=>(p e).coeff j) l (𝓝 (p₀.coeff j)))
    (hdeg : ∀ e,(p e).natDegree≤N) (hdeg₀ : p₀.natDegree≤N)
    (ha : Tendsto a l (𝓝 a₀)) (n : ℕ) :
    Tendsto (fun e=>(p e /ₘ (X-C (a e))).coeff n) l (𝓝 ((p₀ /ₘ (X-C a₀)).coeff n)) := by
  simp_rw [complex_coeff_divByMonic_bounded _ _ (hdeg _) n,
    complex_coeff_divByMonic_bounded _ _ hdeg₀ n]
  exact tendsto_finsetSum _ (fun i _=>(ha.pow _).mul (hp i))

theorem complex_tendsto_eval_of_coeff {A : Type*} {l : Filter A}
    {p : A→Polynomial ℂ} {p₀ : Polynomial ℂ} {z : A→ℂ} {z₀ : ℂ} {N : ℕ}
    (hp : ∀ j,Tendsto (fun e=>(p e).coeff j) l (𝓝 (p₀.coeff j)))
    (hdeg : ∀ e,(p e).natDegree<N) (hdeg₀ : p₀.natDegree<N)
    (hz : Tendsto z l (𝓝 z₀)) :
    Tendsto (fun e=>(p e).eval (z e)) l (𝓝 (p₀.eval z₀)) := by
  simp_rw [eval_eq_sum_range' (hdeg _) _,eval_eq_sum_range' hdeg₀ _]
  exact tendsto_finsetSum _ (fun j _=>(hp j).mul (hz.pow j))

/-- Successive deflation counts repeated limit roots with their multiplicity. -/
theorem exists_two_root_selections {A : Type*} {l : Filter A}
    {p : A→Polynomial ℂ} {p₀ q₀ : Polynomial ℂ} {N : ℕ} {a b : ℂ}
    (hdeg : ∀ e,(p e).natDegree≤N) (hdeg₀ : p₀.natDegree≤N)
    (heval : ∀ z : ℂ,Tendsto (fun e=>(p e).eval z) l (𝓝 (p₀.eval z)))
    (hfac : p₀=(X-C a)*q₀) (hq₀ : q₀≠0) (hb : q₀.eval b=0) :
    ∃ r s : A→ℂ,Tendsto r l (𝓝 a) ∧ Tendsto s l (𝓝 b) ∧
      ∀ᶠ e in l,∃ q : Polynomial ℂ,p e=(X-C (r e))*(X-C (s e))*q := by
  have hp₀ : p₀≠0 := by rw [hfac];exact mul_ne_zero (X_sub_C_ne_zero a) hq₀
  have ha : p₀.eval a=0 := by simp [hfac]
  obtain ⟨r,hr,hroot⟩ := exists_root_selection hdeg heval hp₀ ha
  let q : A→Polynomial ℂ := fun e=>p e /ₘ (X-C (r e))
  have hquot : p₀ /ₘ (X-C a)=q₀ := by rw [hfac,mul_divByMonic_cancel_left _ (monic_X_sub_C a)]
  have hqdeg : ∀ e,(q e).natDegree≤N := by
    intro e
    exact (natDegree_le_natDegree (degree_divByMonic_le _ _)).trans (hdeg e)
  have hqdeg₀ : q₀.natDegree≤N := by
    rw [←hquot]
    exact (natDegree_le_natDegree (degree_divByMonic_le _ _)).trans hdeg₀
  have hc : ∀ n,Tendsto (fun e=>(q e).coeff n) l (𝓝 (q₀.coeff n)) := by
    intro n
    simpa only [q,hquot] using complex_tendsto_divByMonic_coeff
      (tendsto_coeff_of_eval hdeg hdeg₀ heval) hdeg hdeg₀ hr n
  have hqe (z : ℂ) : Tendsto (fun e=>(q e).eval z) l (𝓝 (q₀.eval z)) :=
    complex_tendsto_eval_of_coeff hc (fun e=>(hqdeg e).trans_lt (Nat.lt_succ_self N))
      (hqdeg₀.trans_lt (Nat.lt_succ_self N)) tendsto_const_nhds
  obtain ⟨s,hs,hsroot⟩ := exists_root_selection hqdeg hqe hq₀ hb
  refine ⟨r,s,hr,hs,?_⟩
  filter_upwards [hroot,hsroot] with e he hse
  refine ⟨q e /ₘ (X-C (s e)),?_⟩
  calc
    p e=(X-C (r e))*q e := (mul_divByMonic_eq_iff_isRoot.mpr he).symm
    _=(X-C (r e))*((X-C (s e))*(q e /ₘ (X-C (s e)))) := by
      rw [mul_divByMonic_eq_iff_isRoot.mpr hse]
    _=_ := by ring

end
end nesterov.Slow
