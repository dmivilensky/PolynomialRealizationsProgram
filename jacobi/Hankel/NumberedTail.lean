import jacobi.Hankel.RealZero
import jacobi.Hankel.SquaredExpansion
import jacobi.Hankel.SquaredGeometry
import jacobi.Bessel.GridNumbering

/-!
Article: jacobi, Lemma E.1.
Use: the full Lemma E.1 adjoins the finite prefix on a common smaller disk; the analytic GL construction then uses the resulting complete original spectral sequence.
-/
namespace jacobi.Hankel
noncomputable section
open Set Metric
set_option backward.isDefEq.respectTransparency false

/-- The entire original numbered infinite Bessel spectral tail has one common holomorphic order disk, the printed inverse-square reference error, and genuine quadratic separation.
Use: the full Lemma E.1 adjoins the finite prefix on a common smaller disk; the analytic GL construction then uses the resulting complete original spectral sequence.
Article: jacobi, Lemma E.1.
Proof: square the actual holomorphic frequency branches and apply their proved cubic reciprocal-grid correction. The genuine quarter-disk geometry gives quadratic nonvanishing and separation directly. At real order the earlier singular Green identity makes every actual frequency positive real; the original two-interval phase bound and numbered Weyl phase fix its exact canonical index. -/
theorem uniform_numbered_bessel_tail {a0 : ℝ} (ha0 : -1<a0) :
    ∃ r C : ℝ,∃ N : ℕ,∃ S : ℕ → ℂ → ℂ,
      0<r ∧ r≤1 ∧ r<a0+1 ∧ 0<C ∧ 1≤N ∧
      (∀ k : ℕ,N≤k → DifferentiableOn ℂ (S k) (ball (a0:ℂ) r)) ∧
      (∀ a : ℂ,‖a-(a0:ℂ)‖<r → ∀ k : ℕ,N≤k →
        jacobi.Bessel.normalized a (S k a)=0 ∧
        ‖S k a-frequencyReference a k‖≤C/(k:ℝ)^2 ∧ (k:ℝ)^2≤‖S k a‖) ∧
      (∀ a : ℂ,‖a-(a0:ℂ)‖<r → ∀ k l : ℕ,N≤k → N≤l → k≠l →
        |(l:ℝ)^2-(k:ℝ)^2|≤‖S l a-S k a‖) ∧
      (∀ b : ℝ,∀ hb : -1<b,‖(b:ℂ)-(a0:ℂ)‖<r → ∀ k : ℕ,N≤k →
        S k (b:ℂ)=(jacobi.Bessel.sigma b hb k:ℂ)) := by
  -- Every branch is chosen from the same proved original holomorphic frequency-disk construction.
  classical
  obtain ⟨r,C,N,hr,hr1,hra,hC,hN,hbranches⟩ := uniform_bessel_zero_expansion ha0
  let B : ℝ := (‖(a0:ℂ)‖+1)^2+1
  let Q : ℝ := Real.pi*(1+(‖(a0:ℂ)‖+1)/2+3/4)
  let D : ℝ := 2*Q*C+(C+B/2)^2
  have hB : 0<B := by dsimp [B]; positivity
  have hQ : 0<Q := by dsimp [Q]; positivity
  have hD : 0<D := by dsimp [D]; positivity
  obtain ⟨M,hM⟩ := exists_nat_gt (2*B)
  let L : ℕ := max N M
  have hNL : N≤L := le_max_left _ _
  let u (k : ℕ) : ℂ → ℂ := if hk : N≤k then Classical.choose (hbranches k hk) else fun _ => 0
  have hspec (k : ℕ) (hk : N≤k) :
      DifferentiableOn ℂ (u k) (ball (a0:ℂ) r) ∧ ∀ a : ℂ,‖a-(a0:ℂ)‖<r →
      ‖u k a‖≤1/4 ∧ jacobi.Bessel.normalized a ((frequencyGrid a k+u k a)^2)=0 ∧
      ‖u k a-besselCoefficient a/(2*frequencyGrid a k)‖≤C/(k:ℝ)^3 ∧
      ∀ ζ : ℂ,‖ζ‖≤1/4 → jacobi.Bessel.normalized a ((frequencyGrid a k+ζ)^2)=0 → ζ=u k a := by
    simpa only [u,dite_eq_left hk] using Classical.choose_spec (hbranches k hk)
  let S (k : ℕ) (a : ℂ) : ℂ := (frequencyGrid a k+u k a)^2
  have hreal {a : ℂ} (ha : ‖a-(a0:ℂ)‖<r) : -1<a.re := by
    have hh := Complex.re_le_norm ((a0:ℂ)-a)
    rw [norm_sub_rev] at hh
    simp only [Complex.sub_re,Complex.ofReal_re] at hh
    linarith
  refine ⟨r,D,L,S,hr,hr1,hra,hD,hN.trans hNL,?_,?_,?_,?_⟩
  · intro k hk a ha
    have hq : DifferentiableAt ℂ (fun b => frequencyGrid b k) a := by unfold frequencyGrid; fun_prop
    exact ((hq.differentiableWithinAt.add ((hspec k (hNL.trans hk)).1 a ha)).pow 2)
  · intro a ha k hk
    have hkN := hNL.trans hk
    obtain ⟨hsize,hzero,herror,_hunique⟩ := (hspec k hkN).2 a ha
    have hk1 : 1≤(k:ℝ) := by exact_mod_cast hN.trans hkN
    have hq := (frequencyGrid_disk_geometry ha hr1 (hreal ha) k (by norm_num : ‖(0:ℂ)‖≤1/4)).1
    simp only [add_zero] at hq
    have hc : ‖besselCoefficient a‖≤B := besselCoefficient_unit_bound (ha.le.trans hr1)
    have hupper : ‖frequencyGrid a k‖≤Q*(k:ℝ) := frequencyGrid_upper (ha.le.trans hr1) hk1
    exact ⟨hzero,squared_grid_error hC.le hc hk1 (hq.trans (Complex.re_le_norm _)) hupper herror,
      frequency_disk_squared_lower ha hr1 (hreal ha) k hsize⟩
  · intro a ha k l hk hl hkl
    exact frequency_disks_squared_separated ha hr1 (hreal ha) hkl
      ((hspec k (hNL.trans hk)).2 a ha).1 ((hspec l (hNL.trans hl)).2 a ha).1
  · intro b hb hbDisk k hk
    let w (n : ℕ) : ℝ := (frequencyGrid (b:ℂ) (L+n)+u (L+n) (b:ℂ)).re
    have hroot (n : ℕ) : ∃ m : ℕ,
        frequencyGrid (b:ℂ) (L+n)+u (L+n) (b:ℂ)=(jacobi.Bessel.positiveZero b hb m:ℂ) := by
      have hkn : N≤L+n := hNL.trans (Nat.le_add_right L n)
      have hdata := (hspec (L+n) hkn).2 (b:ℂ) hbDisk
      have hgeom := (frequencyGrid_disk_geometry hbDisk hr1 (by simpa using hb) (L+n) hdata.1).1
      have hindex : 1≤((L+n:ℕ):ℝ) := by exact_mod_cast hN.trans hkn
      exact frequency_zero_real hb (lt_of_lt_of_le zero_lt_one (hindex.trans hgeom)) hdata.2.1
    have hz (n : ℕ) : ∃ m : ℕ,w n= jacobi.Bessel.positiveZero b hb m := by
      obtain ⟨m,hm⟩ := hroot n
      exact ⟨m,by simpa only [w,Complex.ofReal_re] using congrArg Complex.re hm⟩
    have hclose (n : ℕ) : |w n- jacobi.Bessel.phaseGrid b (L+n)|≤1/4 := by
      have hkn : N≤L+n := hNL.trans (Nat.le_add_right L n)
      have hsize := ((hspec (L+n) hkn).2 (b:ℂ) hbDisk).1
      have he : w n- jacobi.Bessel.phaseGrid b (L+n)=(u (L+n) (b:ℂ)).re := by
        dsimp [w]
        rw [(frequencyGrid_coordinates (b:ℂ) (L+n)).1]
        simp only [Complex.ofReal_re]
        unfold jacobi.Bessel.phaseGrid
        ring
      rw [he]
      exact (Complex.abs_re_le_norm _).trans hsize
    have hfar (n : ℕ) : 2*(b^2+1)≤w n := by
      have hkn : N≤L+n := hNL.trans (Nat.le_add_right L n)
      have hsize := ((hspec (L+n) hkn).2 (b:ℂ) hbDisk).1
      have hgeom := (frequencyGrid_disk_geometry hbDisk hr1 (by simpa using hb) (L+n) hsize).1
      have hMk : M≤L+n := (le_max_right N M).trans (Nat.le_add_right L n)
      have hMkR : (M:ℝ)≤((L+n:ℕ):ℝ) := by exact_mod_cast hMk
      have hnorm : |b|≤‖(a0:ℂ)‖+1 := by
        have hh := norm_le_norm_sub_add (b:ℂ) (a0:ℂ)
        rw [Complex.norm_real,Real.norm_eq_abs] at hh
        linarith [hbDisk.le.trans hr1]
      have hbound : b^2+1≤B := by
        have hsquare := pow_le_pow_left₀ (abs_nonneg b) hnorm 2
        rw [sq_abs] at hsquare
        dsimp [B]
        linarith
      change 2*(b^2+1)≤(frequencyGrid (b:ℂ) (L+n)+u (L+n) (b:ℂ)).re
      linarith
    have hnumber := jacobi.Bessel.grid_tail_numbering hb L w hz hclose hfar (k-L)
    have hindex : L+(k-L)=k := Nat.add_sub_of_le hk
    dsimp only [w] at hnumber
    rw [hindex] at hnumber
    obtain ⟨m,hm⟩ := hroot (k-L)
    rw [hindex] at hm
    have hfreqreal : frequencyGrid (b:ℂ) k+u k (b:ℂ)=
        ((frequencyGrid (b:ℂ) k+u k (b:ℂ)).re:ℂ) := by rw [hm]; simp
    have hfreq : frequencyGrid (b:ℂ) k+u k (b:ℂ)=(jacobi.Bessel.positiveZero b hb k:ℂ) :=
      hfreqreal.trans (congrArg Complex.ofReal hnumber)
    change (frequencyGrid (b:ℂ) k+u k (b:ℂ))^2=(jacobi.Bessel.sigma b hb k:ℂ)
    rw [hfreq,← Complex.ofReal_pow,(jacobi.Bessel.positiveZero_properties hb k).2]

end
end jacobi.Hankel
