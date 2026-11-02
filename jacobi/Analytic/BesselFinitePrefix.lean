import jacobi.Analytic.BesselLocalZero
import jacobi.Analytic.FiniteOrderContours
import jacobi.Bessel.FiniteZeroNumbering

/-!
Article: jacobi, Lemma E.1.
Every finite original numbered Bessel prefix has genuine
holomorphic branches on a single common order disk. Compact
zero-free exclusion and the earlier actual zero enumeration fix
the real numbering, rather than assuming branch labels persist.
Use: adjoining these actual branches to uniform_numbered_bessel_tail gives the complete common-disk spectral family in Lemma E.1.
-/
namespace jacobi.Bessel
noncomputable section
open Set Metric Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Every finite original numbered squared-Bessel prefix has a common genuine holomorphic complex-order continuation and agrees with the original real numbered zeros.
Use: adjoining these actual branches to uniform_numbered_bessel_tail gives the complete common-disk spectral family in Lemma E.1.
Article: jacobi, Lemma E.1.
Proof: continue each actual simple zero by the proved local holomorphic zero theorem. Remove small spectral disks around these finitely many original zeros from a fixed initial spectral ball. The remaining compact set is genuinely zero-free by original zero positivity and exhaustive numbering, so the proved compact order stability excludes new roots there. Shrink the order disk to preserve branch ordering and the common upper threshold; actual finite zero coverage then gives the exact original numbering. -/
theorem finite_numbered_bessel_prefix {a0 : ℝ} (ha0 : -1<a0) (N : ℕ) (hN : 0<N) :
    ∃ r : ℝ,∃ V : Fin N → ℂ → ℂ,0<r ∧
      (∀ i : Fin N,DifferentiableOn ℂ (V i) (ball (a0:ℂ) r)) ∧
      (∀ a : ℂ,‖a-(a0:ℂ)‖<r → ∀ i : Fin N,normalized a (V i a)=0) ∧
      (∀ b : ℝ,∀ hb : -1<b,‖(b:ℂ)-(a0:ℂ)‖<r → ∀ i : Fin N,
        V i (b:ℂ)=(sigma b hb i:ℂ)) := by
  -- Every local branch begins at an actual original simple spectral zero.
  classical
  have hex (i : Fin N) := normalized_local_holomorphic_zero
    (by simpa only [Complex.ofReal_re] using ha0) (sigma_mem ha0 i)
  choose rr ss V hrr hss hV hbase hlocal using hex
  have hcont (i : Fin N) : ContinuousAt (V i) (a0:ℂ) :=
    (hV i).continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self (hrr i)))
  let T : ℝ := (sigma a0 ha0 (N-1)+sigma a0 ha0 N)/2
  have hgap : sigma a0 ha0 (N-1)<sigma a0 ha0 N := sigma_strictMono ha0 (by omega)
  have hT : 0<T := by have hp := spectralZero_pos ha0 (sigma_mem ha0 (N-1)); dsimp [T]; linarith
  have hbelow (i : Fin N) : sigma a0 ha0 i<T := by
    have hh := (sigma_strictMono ha0).monotone (show i.val≤N-1 from by omega)
    dsimp [T]
    linarith
  let K : Set ℂ := closedBall (0:ℂ) T \ ⋃ i : Fin N,ball (sigma a0 ha0 i:ℂ) (ss i/2)
  have hK : IsCompact K := (isCompact_closedBall (0:ℂ) T).diff (isOpen_iUnion fun _ => isOpen_ball)
  have hfree : ∀ z∈K,normalized (a0:ℂ) z≠0 := by
    intro z hz hzero
    obtain ⟨x,hxp,hx⟩ := normalized_zero_positive ha0 hzero
    have hxzero : x∈spectralZeros a0 := by change normalized (a0:ℂ) (x:ℂ)=0; rw [← hx]; exact hzero
    obtain ⟨m,hm⟩ := sigma_exhaustive ha0 hxzero
    have hn : ‖z‖≤T := by simpa only [mem_closedBall,dist_zero_right] using hz.1
    rw [hx,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hxp] at hn
    have hmN : m<N := by
      by_contra hnot
      have hh := (sigma_strictMono ha0).monotone (not_lt.mp hnot)
      rw [hm] at hh
      dsimp [T] at hn
      linarith
    let i : Fin N := ⟨m,hmN⟩
    have hball : z∈ball (sigma a0 ha0 i:ℂ) (ss i/2) := by
      change dist z (sigma a0 ha0 m:ℂ)<ss i/2
      rw [hm,hx,dist_self]
      exact half_pos (hss i)
    exact hz.2 (mem_iUnion.mpr ⟨i,hball⟩)
  obtain ⟨r0,c,hr0,hc,hbound⟩ := compact_order_contour_bound (by simpa using ha0) hK hfree
  have hnearlocal : ∀ᶠ a : ℂ in 𝓝 (a0:ℂ),∀ i : Fin N,a∈ball (a0:ℂ) (rr i) :=
    eventually_all.mpr (fun i => ball_mem_nhds (a0:ℂ) (hrr i))
  have hnearbelow : ∀ᶠ a : ℂ in 𝓝 (a0:ℂ),∀ i : Fin N,(V i a).re<T := by
    apply eventually_all.mpr
    intro i
    apply (Complex.continuous_re.continuousAt.comp (hcont i)).eventually_lt_const
    change (V i (a0:ℂ)).re<T
    rw [hbase i,Complex.ofReal_re]
    exact hbelow i
  have hnearorder : ∀ᶠ a : ℂ in 𝓝 (a0:ℂ),∀ i j : Fin N,i<j → (V i a).re<(V j a).re := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hij : i<j
    · have hbaseorder : (V i (a0:ℂ)).re<(V j (a0:ℂ)).re := by
        rw [hbase i,hbase j,Complex.ofReal_re,Complex.ofReal_re]
        exact sigma_strictMono ha0 hij
      exact ((Complex.continuous_re.continuousAt.comp (hcont i)).eventually_lt
        (Complex.continuous_re.continuousAt.comp (hcont j)) hbaseorder).mono (fun _ hh _ => hh)
    · exact Eventually.of_forall (fun _ hh => (hij hh).elim)
  obtain ⟨r,hr,hrdata⟩ := Metric.mem_nhds_iff.mp
    ((show ∀ᶠ a : ℂ in 𝓝 (a0:ℂ),a∈ball (a0:ℂ) r0 from ball_mem_nhds (a0:ℂ) hr0).and (hnearlocal.and (hnearbelow.and hnearorder)))
  have hdata (a : ℂ) (ha : a∈ball (a0:ℂ) r) := hrdata ha
  refine ⟨r,V,hr,?_,?_,?_⟩
  · intro i
    exact (hV i).mono (fun a ha => (hdata a ha).2.1 i)
  · intro a ha i
    have ha' : a∈ball (a0:ℂ) r := by simpa only [mem_ball,dist_eq_norm] using ha
    exact (hlocal i a (by simpa only [mem_ball,dist_eq_norm] using (hdata a ha').2.1 i)).2.2.1
  · intro b hb hbDisk
    have hb' : (b:ℂ)∈ball (a0:ℂ) r := by simpa only [mem_ball,dist_eq_norm] using hbDisk
    have hloc (i : Fin N) := hlocal i (b:ℂ)
      (by simpa only [mem_ball,dist_eq_norm] using (hdata (b:ℂ) hb').2.1 i)
    let w (i : Fin N) : ℝ := (V i (b:ℂ)).re
    have hre (i : Fin N) : V i (b:ℂ)=(w i:ℂ) := by
      obtain ⟨x,_hx,hx⟩ := normalized_zero_positive hb (hloc i).2.2.1
      rw [hx]
      simp only [w,hx,Complex.ofReal_re]
    have hz (i : Fin N) : w i∈spectralZeros b := by
      change normalized (b:ℂ) (w i:ℂ)=0
      rw [← hre]
      exact (hloc i).2.2.1
    have hmono : StrictMono w := (hdata (b:ℂ) hb').2.2.2
    have hwb : ∀ i,w i<T := (hdata (b:ℂ) hb').2.2.1
    have hcover (x : ℝ) (hx : x∈spectralZeros b) (hxt : x<T) : ∃ i : Fin N,w i=x := by
      have hxp := spectralZero_pos hb hx
      have hinside : (x:ℂ)∈closedBall (0:ℂ) T := by
        rw [mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hxp]
        exact hxt.le
      have hexball : ∃ i : Fin N,(x:ℂ)∈ball (sigma a0 ha0 i:ℂ) (ss i/2) := by
        by_contra hn
        have hxK : (x:ℂ)∈K := ⟨hinside,by simpa only [mem_iUnion,not_exists] using hn⟩
        have hh := ((hbound (b:ℂ) (hdata (b:ℂ) hb').1).2 (x:ℂ) hxK)
        change normalized (b:ℂ) (x:ℂ)=0 at hx
        rw [hx,norm_zero] at hh
        linarith
      obtain ⟨i,hi⟩ := hexball
      have hsmall : ‖(x:ℂ)-(sigma a0 ha0 i:ℂ)‖≤ss i := by
        have hh : ‖(x:ℂ)-(sigma a0 ha0 i:ℂ)‖<ss i/2 := by simpa only [mem_ball,dist_eq_norm] using hi
        linarith [hss i]
      have he := (hloc i).2.2.2 (x:ℂ) hsmall hx
      exact ⟨i,by simpa only [w,Complex.ofReal_re] using (congrArg Complex.re he).symm⟩
    intro i
    exact (hre i).trans (congrArg Complex.ofReal (finite_zero_numbering hb w hz hmono hwb hcover i))

end
end jacobi.Bessel
