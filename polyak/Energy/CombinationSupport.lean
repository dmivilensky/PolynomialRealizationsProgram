import polyak.Energy.FiniteCombination

/-!
Article: Appendix C, the exact finite width of interpolation kernels.
Use: lags at most five and the two recurrence neighbors give precisely the
source shifts −1,…,6 needed by the common width-seven construction.
-/
noncomputable section
namespace polyak.Energy

def FilterSupported (a b : ℤ) (L : LinearFilter) : Prop :=
  ∀ p∈L,a≤p.2 ∧ p.2≤b

def KernelSupported (a b : ℤ) (K : Kernel) : Prop :=
  ∀ p∈K,(a≤p.2.1 ∧ p.2.1≤b) ∧ (a≤p.2.2 ∧ p.2.2≤b)

theorem FilterSupported.weaken {a b c d : ℤ} {L : LinearFilter}
    (h : FilterSupported a b L) (hca : c≤a) (hbd : b≤d) : FilterSupported c d L := by
  intro p hp
  exact ⟨hca.trans (h p hp).1,(h p hp).2.trans hbd⟩

theorem FilterSupported.append {a b : ℤ} {L M : LinearFilter}
    (hL : FilterSupported a b L) (hM : FilterSupported a b M) : FilterSupported a b (L++M) := by
  intro p hp
  exact (List.mem_append.mp hp).elim (hL p) (hM p)

theorem FilterSupported.scale {a b : ℤ} {L : LinearFilter}
    (hL : FilterSupported a b L) (r : ℝ) : FilterSupported a b (filterScale r L) := by
  intro p hp
  obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
  exact hL q hq

theorem FilterSupported.shift {a b : ℤ} {L : LinearFilter}
    (hL : FilterSupported a b L) (n : ℤ) : FilterSupported (a+n) (b+n) (filterShift n L) := by
  intro p hp
  obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
  have hh:=hL q hq
  change a+n≤n+q.2 ∧ n+q.2≤b+n
  omega

theorem KernelSupported.append {a b : ℤ} {K L : Kernel}
    (hK : KernelSupported a b K) (hL : KernelSupported a b L) : KernelSupported a b (K++L) := by
  intro p hp
  exact (List.mem_append.mp hp).elim (hK p) (hL p)

theorem KernelSupported.scale {a b : ℤ} {K : Kernel}
    (hK : KernelSupported a b K) (r : ℝ) : KernelSupported a b (kernelScale r K) := by
  intro p hp
  obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp
  exact hK q hq

theorem KernelSupported.outer {a b : ℤ} {L M : LinearFilter}
    (hL : FilterSupported a b L) (hM : FilterSupported a b M) : KernelSupported a b (filterOuter L M) := by
  intro p hp
  obtain ⟨q,hq,hp⟩:=List.mem_flatMap.mp hp
  obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hp
  exact ⟨hL q hq,hM r hr⟩

theorem KernelSupported.flatMap {a b : ℤ} {I : Type*} {L : List I} {K : I → Kernel}
    (h : ∀ i∈L,KernelSupported a b (K i)) : KernelSupported a b (L.flatMap K) := by
  intro p hp
  obtain ⟨i,hi,hp⟩:=List.mem_flatMap.mp hp
  exact h i hi p hp

theorem pairKernel_supported {a b : ℤ} {X Y S T : LinearFilter}
    (hX : FilterSupported a b X) (hY : FilterSupported a b Y)
    (hS : FilterSupported a b S) (hT : FilterSupported a b T) (δ : ℝ) :
    KernelSupported a b (pairKernel δ X Y S T) := by
  have hYX : FilterSupported a b (filterDifference Y X):=hY.append (hX.scale _)
  have hTS : FilterSupported a b (filterDifference T S):=hT.append (hS.scale _)
  exact (((KernelSupported.outer hYX hYX).scale _).append
    ((KernelSupported.outer hTS hTS).scale _)).append
      ((KernelSupported.outer (hS.append hT) hYX).scale _)

theorem starKernel_supported {a b : ℤ} {X S : LinearFilter}
    (hX : FilterSupported a b X) (hS : FilterSupported a b S) (δ : ℝ) :
    KernelSupported a b (starKernel δ X S) :=
  (((KernelSupported.outer hX hX).scale _).append
    ((KernelSupported.outer hS hS).scale _)).append ((KernelSupported.outer hS hX).scale _)

theorem unitFilter_supported : FilterSupported 0 0 unitFilter := by
  intro p hp
  have he : p=(1,0):=List.mem_singleton.mp hp
  subst p
  exact ⟨le_rfl,le_rfl⟩

theorem gradientFilter_supported (A B β t : ℝ) : FilterSupported (-1) 1 (gradientFilter A B β t) := by
  intro p hp
  simp only [gradientFilter,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl <;> norm_num

theorem lagKernel_supported (A B β t : ℝ) (N n : ℕ) (hn : n≤N) (δ : ℝ) :
    KernelSupported (-1) ((N : ℤ)+1) (lagKernel A B β t n δ) := by
  have hu:=unitFilter_supported.weaken (by omega : (-1 : ℤ)≤0) (by omega : (0 : ℤ)≤(N : ℤ)+1)
  have hy:=((unitFilter_supported.shift (n : ℤ)).weaken
    (by omega : (-1 : ℤ)≤0+(n : ℤ)) (by omega : (0 : ℤ)+(n : ℤ)≤(N : ℤ)+1)).scale (Real.exp (n*t))
  have hg:=(gradientFilter_supported A B β t).weaken le_rfl (by omega : (1 : ℤ)≤(N : ℤ)+1)
  have ht:=(((gradientFilter_supported A B β t).shift (n : ℤ)).weaken
    (by omega : (-1 : ℤ)≤ -1+(n : ℤ)) (by omega : (1 : ℤ)+(n : ℤ)≤(N : ℤ)+1)).scale (Real.exp (n*t))
  exact pairKernel_supported hu hy hg ht δ

theorem combinationKernel_supported {t : ℝ} (A B β : ℝ) (comb : FiniteCombination t)
    (N : ℕ) (hN : ∀ n∈comb.lags,n≤N) :
    KernelSupported (-1) ((N : ℤ)+1) (combinationKernel A B β t comb) := by
  have hlag : KernelSupported (-1) ((N : ℤ)+1)
      (comb.lags.toList.flatMap fun (n : ℕ) => kernelScale (2*Real.exp (-(n*t)))
        (kernelScale (comb.α n) (lagKernel A B β t n 1)++
          kernelScale (comb.β n) (lagKernel A B β t n (-1)))) := by
    apply KernelSupported.flatMap
    intro n hn
    have hn':=hN n (Finset.mem_toList.mp hn)
    exact (((lagKernel_supported A B β t N n hn' 1).scale _).append
      ((lagKernel_supported A B β t N n hn' (-1)).scale _)).scale _
  have hu:=unitFilter_supported.weaken (by omega : (-1 : ℤ)≤0) (by omega : (0 : ℤ)≤(N : ℤ)+1)
  have hg:=(gradientFilter_supported A B β t).weaken le_rfl (by omega : (1 : ℤ)≤(N : ℤ)+1)
  exact (hlag.append ((starKernel_supported hu hg 1).scale _)).append
    ((starKernel_supported hu hg (-1)).scale _)

end polyak.Energy
