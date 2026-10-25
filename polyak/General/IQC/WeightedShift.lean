import polyak.General.IQC.Sequence

/-! Article: Appendix D, Lemma shift. Restarted weighted energy contracts
every second tail with exactly the source's factor C'/(1+C'). -/
noncomputable section
namespace polyak.General.IQC
open Filter
open scoped Topology

def tailEnergy (b : ℕ → ℝ) (k : ℕ) : ℝ := ∑' j,b (k+j)

theorem tailEnergy_split {b : ℕ → ℝ} (hs : Summable b) (k : ℕ) :
    tailEnergy b k=b k+tailEnergy b (k+1) := by
  have hh : Summable (fun j => b (k+j)):=by
    simpa only [Nat.add_comm] using (summable_nat_add_iff k).mpr hs
  simpa only [tailEnergy,Nat.add_zero,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
    using hh.tsum_eq_zero_add

theorem tailEnergy_nonneg {b : ℕ → ℝ} (hb : ∀ k,0≤b k) (k : ℕ) :
    0≤tailEnergy b k:=tsum_nonneg (fun j => hb (k+j))

theorem tailEnergy_mono {b : ℕ → ℝ} (hs : Summable b) (hb : ∀ k,0≤b k) (k : ℕ) :
    tailEnergy b (k+1)≤tailEnergy b k:=by
  rw [tailEnergy_split hs k]
  linarith [hb k]

theorem energy_le_tail {b : ℕ → ℝ} (hs : Summable b) (hb : ∀ k,0≤b k) (k : ℕ) :
    b k≤tailEnergy b k:=by
  rw [tailEnergy_split hs k]
  linarith [tailEnergy_nonneg hb (k+1)]

theorem two_step_tail_bound {S : ℕ → ℝ} {θ : ℝ} (hθ : 0≤θ)
    (hbase : S 1≤S 0) (hstep : ∀ k,S (k+2)≤θ*S k) (k : ℕ) :
    S k≤θ^(k/2)*S 0:=by
  induction k using Nat.twoStepInduction with
  | zero => simp
  | one => simpa only [Nat.reduceDiv,pow_zero,one_mul] using hbase
  | more k ih _ =>
    calc
      S (k+2)≤θ*S k:=hstep k
      _≤θ*(θ^(k/2)*S 0):=mul_le_mul_of_nonneg_left ih hθ
      _=θ^((k+2)/2)*S 0:=by rw [show (k+2)/2=k/2+1 by omega,pow_succ]; ring

/-- Literal two-step contraction factor from a uniform restarted energy bound. -/
theorem weighted_tail_bound {b : ℕ → ℝ} (hs : Summable b) (hb : ∀ k,0≤b k)
    {C q : ℝ} (hC : 0<C) (_hq : 0≤q)
    (hbound : ∀ k,tailEnergy b (k+1)≤C*(b (k+1)+q*b k)) (k : ℕ) :
    b k≤(C*max 1 q/(1+C*max 1 q))^(k/2)*tailEnergy b 0 := by
  let D:=C*max 1 q
  have hD : 0<D:=mul_pos hC (lt_of_lt_of_le (by norm_num : (0 : ℝ)<1) (le_max_left _ _))
  have hDC : C≤D:=by dsimp [D]; nlinarith [le_max_left (1 : ℝ) q]
  have hDCq : C*q≤D:=mul_le_mul_of_nonneg_left (le_max_right (1 : ℝ) q) hC.le
  have hθ : 0≤D/(1+D):=div_nonneg hD.le (by linarith)
  have hstep (n : ℕ) : tailEnergy b (n+2)≤(D/(1+D))*tailEnergy b n:=by
    have hs0:=tailEnergy_split hs n
    have hs1:=tailEnergy_split hs (n+1)
    have hm:=tailEnergy_mono hs hb (n+1)
    have hh:=hbound n
    have h0:=mul_le_mul_of_nonneg_right hDCq (hb n)
    have h1:=mul_le_mul_of_nonneg_right hDC (hb (n+1))
    have hi : (1+D)*tailEnergy b (n+2)≤D*tailEnergy b n:=by nlinarith
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by linarith : (0 : ℝ)<1+D)).mpr
    nlinarith [hi]
  exact (energy_le_tail hs hb k).trans
    (two_step_tail_bound hθ (tailEnergy_mono hs hb 0) hstep k)

end polyak.General.IQC
