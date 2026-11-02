import jacobi.Analytic.BesselFinitePrefix
import jacobi.Hankel.NumberedTail

/-!
Article: jacobi, Lemma E.1.
Use: the remaining finite-to-infinite separation argument completes Lemma E.1; the analytic GL construction uses this same full original family.
-/
namespace jacobi.Bessel
noncomputable section
open Set Metric Filter jacobi.Hankel
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The full original numbered Bessel zero list has genuine holomorphic branches on one common complex-order disk, with the printed all-index inverse-square reference error.
Use: the remaining finite-to-infinite separation argument completes Lemma E.1; the analytic GL construction uses this same full original family.
Article: jacobi, Lemma E.1.
Proof: intersect the actual finite-prefix and infinite-tail order disks and join their genuine original numbered branches. Near the real center, each finite original error is bounded by its center norm plus one; a finite weighted sum absorbs every prefix index into the same inverse-square constant. The tail estimate is converted from k^(-2) to (k+1)^(-2), retaining the article's one-based index. -/
theorem full_numbered_bessel_family {a0 : ℝ} (ha0 : -1<a0) :
    ∃ r C : ℝ,∃ N : ℕ,∃ S : ℕ → ℂ → ℂ,0<r ∧ r≤1 ∧ r<a0+1 ∧ 0<C ∧ 1≤N ∧
      (∀ k : ℕ,DifferentiableOn ℂ (S k) (ball (a0:ℂ) r)) ∧
      (∀ a : ℂ,‖a-(a0:ℂ)‖<r → ∀ k : ℕ,normalized a (S k a)=0 ∧
        ‖S k a-frequencyReference a k‖≤C/(k+1:ℝ)^2) ∧
      (∀ b : ℝ,∀ hb : -1<b,‖(b:ℂ)-(a0:ℂ)‖<r → ∀ k : ℕ,S k (b:ℂ)=(sigma b hb k:ℂ)) ∧
      (∀ a : ℂ,‖a-(a0:ℂ)‖<r → ∀ k : ℕ,N≤k → (k:ℝ)^2≤‖S k a‖) ∧
      (∀ a : ℂ,‖a-(a0:ℂ)‖<r → ∀ k l : ℕ,N≤k → N≤l → k≠l →
        |(l:ℝ)^2-(k:ℝ)^2|≤‖S l a-S k a‖) := by
  -- Both source constructions retain the actual original real numbering before they are joined.
  classical
  obtain ⟨rt,C,N,T,hrt,hrt1,hrta,hC,hN,hTa,hTe,hTr,hTreal⟩ := uniform_numbered_bessel_tail ha0
  obtain ⟨rp,V,hrp,hVa,hVz,hVreal⟩ := finite_numbered_bessel_prefix ha0 N (by omega)
  let r0 : ℝ := min rt rp
  have hr0 : 0<r0 := lt_min hrt hrp
  let S (k : ℕ) : ℂ → ℂ := if hk : k<N then V ⟨k,hk⟩ else T k
  have hSanalytic (k : ℕ) : DifferentiableOn ℂ (S k) (ball (a0:ℂ) r0) := by
    by_cases hk : k<N
    · simpa only [S,dite_eq_left hk] using (hVa ⟨k,hk⟩).mono (ball_subset_ball (min_le_right _ _))
    · simpa only [S,dite_eq_right hk] using (hTa k (not_lt.mp hk)).mono (ball_subset_ball (min_le_left _ _))
  have hSreal (b : ℝ) (hb : -1<b) (ha : ‖(b:ℂ)-(a0:ℂ)‖<r0) (k : ℕ) : S k (b:ℂ)=(sigma b hb k:ℂ) := by
    by_cases hk : k<N
    · simpa only [S,dite_eq_left hk] using hVreal b hb (ha.trans_le (min_le_right _ _)) ⟨k,hk⟩
    · simpa only [S,dite_eq_right hk] using hTreal b hb (ha.trans_le (min_le_left _ _)) k (not_lt.mp hk)
  have hnear : ∀ᶠ a : ℂ in 𝓝 (a0:ℂ),∀ i : Fin N,
      ‖S i a-frequencyReference a i‖<‖S i (a0:ℂ)-frequencyReference (a0:ℂ) i‖+1 := by
    apply eventually_all.mpr
    intro i
    have hS := (hSanalytic i).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr0))
    have hRef : ContinuousAt (fun a => frequencyReference a i) (a0:ℂ) := by
      unfold frequencyReference frequencyGrid besselCoefficient
      fun_prop
    exact (hS.continuousAt.sub hRef).norm.eventually_lt_const (by
      change ‖S i (a0:ℂ)-frequencyReference (a0:ℂ) i‖<‖S i (a0:ℂ)-frequencyReference (a0:ℂ) i‖+1
      linarith)
  obtain ⟨ρ,hρ,hρdata⟩ := Metric.mem_nhds_iff.mp
    ((show ∀ᶠ a : ℂ in 𝓝 (a0:ℂ),a∈ball (a0:ℂ) r0 from ball_mem_nhds (a0:ℂ) hr0).and hnear)
  let r : ℝ := min ρ r0
  have hr : 0<r := lt_min hρ hr0
  have hrad : r≤r0 := min_le_right _ _
  have hrdata : ball (a0:ℂ) r ⊆ {a | a∈ball (a0:ℂ) r0 ∧ ∀ i : Fin N,
      ‖S i a-frequencyReference a i‖<‖S i (a0:ℂ)-frequencyReference (a0:ℂ) i‖+1} :=
    fun _ ha => hρdata (ball_subset_ball (min_le_left ρ r0) ha)
  let D : ℝ := 4*C+1+∑ i : Fin N,(‖S i (a0:ℂ)-frequencyReference (a0:ℂ) i‖+1)*(i+1:ℝ)^2
  have hD : 0<D := by dsimp [D]; positivity
  refine ⟨r,D,N,S,hr,hrad.trans ((min_le_left _ _).trans hrt1),
    hrad.trans_lt ((min_le_left _ _).trans_lt hrta),hD,hN,
    (fun k => (hSanalytic k).mono (ball_subset_ball hrad)),?_,?_,?_,?_⟩
  · intro a ha k
    have ha' : a∈ball (a0:ℂ) r := by simpa only [mem_ball,dist_eq_norm] using ha
    have har0 : ‖a-(a0:ℂ)‖<r0 := by simpa only [mem_ball,dist_eq_norm] using (hrdata ha').1
    by_cases hk : k<N
    · have hz := hVz a (har0.trans_le (min_le_right _ _)) ⟨k,hk⟩
      refine ⟨by simpa only [S,dite_eq_left hk] using hz,?_⟩
      have hv := (hrdata ha').2 ⟨k,hk⟩
      have hsum := Finset.single_le_sum (f := fun i : Fin N =>
        (‖S i (a0:ℂ)-frequencyReference (a0:ℂ) i‖+1)*(i+1:ℝ)^2)
        (fun i _ => by positivity) (Finset.mem_univ (⟨k,hk⟩:Fin N))
      have hkp : 0<(k+1:ℝ)^2 := by positivity
      apply (le_div_iff₀ hkp).mpr
      dsimp only [Fin.val_mk] at hv hsum
      have hh := mul_le_mul_of_nonneg_right hv.le hkp.le
      dsimp only [D]
      linarith
    · have hkt := not_lt.mp hk
      have hh := hTe a (har0.trans_le (min_le_left _ _)) k hkt
      refine ⟨by simpa only [S,dite_eq_right hk] using hh.1,?_⟩
      have hk1 : 1≤(k:ℝ) := by exact_mod_cast hN.trans hkt
      have hks : (k+1:ℝ)^2≤4*(k:ℝ)^2 := by nlinarith
      have hconv : C/(k:ℝ)^2≤4*C/(k+1:ℝ)^2 := by
        apply (div_le_div_iff₀ (by positivity : 0<(k:ℝ)^2) (by positivity : 0<(k+1:ℝ)^2)).mpr
        nlinarith
      have hconst : 4*C≤D := by
        have hs : 0≤∑ i : Fin N,(‖S i (a0:ℂ)-frequencyReference (a0:ℂ) i‖+1)*(i+1:ℝ)^2 :=
          Finset.sum_nonneg (fun i _ => by positivity)
        dsimp [D]
        linarith
      simpa only [S,dite_eq_right hk] using hh.2.1.trans
        (hconv.trans (div_le_div_of_nonneg_right hconst (by positivity)))
  · intro b hb ha k
    exact hSreal b hb (ha.trans_le hrad) k
  · intro a ha k hk
    have hkn : ¬k<N := not_lt.mpr hk
    simpa only [S,dite_eq_right hkn] using (hTe a ((ha.trans_le hrad).trans_le (min_le_left _ _)) k hk).2.2
  · intro a ha k l hk hl hkl
    have hkn : ¬k<N := not_lt.mpr hk
    have hln : ¬l<N := not_lt.mpr hl
    simpa only [S,dite_eq_right hkn,dite_eq_right hln] using
      hTr a ((ha.trans_le hrad).trans_le (min_le_left _ _)) k l hk hl hkl

end
end jacobi.Bessel
