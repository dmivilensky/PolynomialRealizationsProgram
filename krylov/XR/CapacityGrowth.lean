import krylov.XR.MemoryCapacity
import Mathlib.Order.SuccPred.Archimedean

/-!
Article: main_krylov, thm:grow, deterministic capacity-growth backend.
Use: prove that the literal clean-phase memory recurrence reaches the
configured maximum capacity and fills it. The recurrence is the actual
updateCapacity rule with one accepted positive pair and no deletion.
Source: bounded monotone natural sequences stabilize; a smaller stable
capacity would force the bounded clean counter to increase forever.
-/
namespace krylov.XR
noncomputable section

/-- The exact real capacity update in a one-evaluation, no-deletion
iteration, before assuming its window is full. Article: thm:grow. -/
theorem updateCapacity_unit_no_delete (P : Parameters) (n cap clean len : ℕ)
    (hcap : cap≤n) (hq : 0<P.cleanPeriod) :
    updateCapacity P n cap clean (min cap len) 0 1=
      if cap≤len then
        if clean+1=P.cleanPeriod then (min (cap+P.initialCapacity) P.maximumCapacity,0)
        else (cap,clean+1)
      else (cap,0) := by
  by_cases hfull : cap≤len
  · simpa only [min_eq_left hfull,min_eq_left hcap,ite_eq_left hfull] using updateCapacity_clean P n cap clean
  · have hm : min cap len≠min cap n := by rw [min_eq_left hcap]; omega
    simp [updateCapacity,hm,hfull,hq.ne]

/-- Once the genuine local clean phase starts, the literal capacity
recurrence eventually reaches its configured maximum and the incoming
memory fills that capacity. No eventual-growth assertion is an input.
Article: main_krylov, thm:grow. -/
theorem capacity_growth_eventually (P : Parameters) (n : ℕ)
    (hinitial : 0<P.initialCapacity) (hmaximum : P.maximumCapacity≤n) (hq : 0<P.cleanPeriod)
    (cap clean len : ℕ → ℕ)
    (hcap : ∀ k,cap k≤P.maximumCapacity) (hclean : ∀ k,clean k<P.cleanPeriod)
    (hlen : ∀ k,len (k+1)=min (cap k) (len k)+1)
    (hstep : ∀ k,(cap (k+1),clean (k+1))=
      updateCapacity P n (cap k) (clean k) (min (cap k) (len k)) 0 1) :
    ∃ K,∀ k,K≤k → cap k=P.maximumCapacity ∧ P.maximumCapacity≤len k := by
  have hmono : Monotone cap := monotone_nat_of_le_succ (fun k=>by
    have hh := hstep k
    rw [updateCapacity_unit_no_delete P n _ _ _ ((hcap k).trans hmaximum) hq] at hh
    split_ifs at hh with hfull htrigger
    · have hc := congrArg Prod.fst hh
      have hu := hcap k
      omega
    · have hc := congrArg Prod.fst hh
      simpa only [Prod.fst] using hc.ge
    · have hc := congrArg Prod.fst hh
      simpa only [Prod.fst] using hc.ge)
  have hbounded : BddAbove (Set.range cap) := ⟨P.maximumCapacity,by
    rintro c ⟨k,rfl⟩
    exact hcap k⟩
  obtain ⟨C,hC⟩ := hbounded.exists_isGreatest_of_nonempty ⟨cap 0,⟨0,rfl⟩⟩
  obtain ⟨K,hK⟩ := hC.1
  have hstable (k : ℕ) (hk : K≤k) : cap k=C := by
    apply le_antisymm (hC.2 ⟨k,rfl⟩)
    rw [←hK]
    exact hmono hk
  have hfill (j : ℕ) : min j C≤len (K+j) := by
    induction j with
    | zero => simp only [Nat.zero_min,Nat.add_zero,Nat.zero_le]
    | succ j ih =>
      have hh := hlen (K+j)
      rw [hstable _ (by omega)] at hh
      have he : K+(j+1)=K+j+1 := by omega
      rw [he]
      omega
  have hfilled (k : ℕ) (hk : K+C≤k) : C≤len k := by
    have hj : C≤k-K := by omega
    have hh := hfill (k-K)
    rw [min_eq_right hj,Nat.add_sub_of_le (by omega : K≤k)] at hh
    exact hh
  have hCmax : C=P.maximumCapacity := by
    have hCle : C≤P.maximumCapacity := hK ▸ hcap K
    by_contra hne
    have hClt : C<P.maximumCapacity := by omega
    have hinc (k : ℕ) (hk : K+C≤k) : clean (k+1)=clean k+1 := by
      have hc := hstable k (by omega)
      have hc' := hstable (k+1) (by omega)
      have hh := hstep k
      rw [updateCapacity_unit_no_delete P n _ _ _ ((hcap k).trans hmaximum) hq,
        hc,ite_eq_left (hfilled k hk)] at hh
      split_ifs at hh with htrigger
      · have he := congrArg Prod.fst hh
        omega
      · have he := congrArg Prod.snd hh
        simpa only [Prod.snd] using he
    have hcount (j : ℕ) : clean (K+C+j)=clean (K+C)+j := by
      induction j with
      | zero => simp only [Nat.add_zero]
      | succ j ih =>
        have hh := hinc (K+C+j) (by omega)
        have he : K+C+(j+1)=K+C+j+1 := by omega
        rw [he]
        omega
    have hh := hclean (K+C+P.cleanPeriod)
    rw [hcount] at hh
    omega
  refine ⟨K+C,fun k hk=>?_⟩
  exact ⟨(hstable k (by omega)).trans hCmax,hCmax ▸ hfilled k hk⟩

/-- The same actual recurrence may start at any late source index.
Article: main_krylov, thm:grow, application after primitive local activation. -/
theorem capacity_growth_eventually_of_tail (P : Parameters) (n K₀ : ℕ)
    (hinitial : 0<P.initialCapacity) (hmaximum : P.maximumCapacity≤n) (hq : 0<P.cleanPeriod)
    (cap clean len : ℕ → ℕ)
    (hcap : ∀ k,cap k≤P.maximumCapacity) (hclean : ∀ k,clean k<P.cleanPeriod)
    (hlen : ∀ k,K₀≤k → len (k+1)=min (cap k) (len k)+1)
    (hstep : ∀ k,K₀≤k → (cap (k+1),clean (k+1))=
      updateCapacity P n (cap k) (clean k) (min (cap k) (len k)) 0 1) :
    ∃ K,∀ k,K≤k → cap k=P.maximumCapacity ∧ P.maximumCapacity≤len k := by
  obtain ⟨K,hK⟩ := capacity_growth_eventually P n hinitial hmaximum hq
    (fun j=>cap (K₀+j)) (fun j=>clean (K₀+j)) (fun j=>len (K₀+j))
    (fun j=>hcap _) (fun j=>hclean _)
    (fun j=>by simpa only [Nat.add_assoc] using hlen (K₀+j) (by omega))
    (fun j=>by simpa only [Nat.add_assoc] using hstep (K₀+j) (by omega))
  refine ⟨K₀+K,fun k hk=>?_⟩
  have hh := hK (k-K₀) (by omega)
  simpa only [Nat.add_sub_of_le (by omega : K₀≤k)] using hh

end
end krylov.XR
