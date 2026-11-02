import jacobi.Complex.JensenBlocks
import Mathlib.Analysis.Real.Pi.Bounds

/-!
Article: jacobi, Proposition 2.2.
An entire function of exponential type at most one half that vanishes
at both signs of a positive strictly enumerated root sequence bounded
above by pi*k plus a constant is zero. This proves the actual uniqueness
principle used in GL positivity, retaining the full finite Jensen mass.
Source: Levin, Distribution of Zeros of Entire Functions, Jensen's formula.
Use: the actual source reference coefficient transform vanishes identically when all its Bessel spectral coefficients vanish; Parseval then gives GL injectivity.
-/
namespace jacobi.Complex
noncomputable section
open Real Set Metric
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Entire functions of the source half-interval exponential type are uniquely determined by their values at both signs of the original pi-spaced spectral roots.
Use: the actual source reference coefficient transform vanishes identically when all its Bessel spectral coefficients vanish; Parseval then gives GL injectivity.
Article: jacobi, Proposition 2.2.
Source: Levin, Distribution of Zeros of Entire Functions, Jensen's formula.
Proof: center Jensen's formula at an actual nonzero value, if one exists.
Group the first sixteen N positive and negative roots into sixteen
equal blocks. Their logarithmic contribution is at least
2*N*blockLogMass, while true type one half gives at most 8*pi*N plus
a fixed constant. The strict universal excess contradicts arbitrarily
large natural N. No density asymptotic or zero-count certificate is used. -/
theorem eq_zero_of_signed_roots_type_half {f : ℂ → ℂ} (hf : ∀ z,AnalyticAt ℂ f z)
    {x : ℕ → ℝ} (hx : StrictMono x) (hp : ∀ k,0<x k)
    (hbound : ∃ D:ℝ,0<D ∧ ∀ k,x k≤Real.pi*(k+D))
    (hzero : ∀ k,f (x k:ℂ)=0 ∧ f (-(x k:ℂ))=0)
    (hgrowth : ∃ C:ℝ,0<C ∧ ∀ z,‖f z‖≤C*Real.exp (‖z‖/2)) : f=0 := by
  classical
  -- A nonzero center avoids factoring an unknown zero order at the frequency origin.
  by_contra hfzero
  obtain ⟨c,hc⟩ : ∃ c,f c≠0 := by
    by_contra h
    push Not at h
    exact hfzero (funext h)
  obtain ⟨D,hD,hbound⟩ := hbound
  obtain ⟨C,hC,hgrowth⟩ := hgrowth
  let M := C+1
  have hM : 1≤M := by dsimp [M]; linarith
  have hMbound (z : ℂ) : ‖f z‖≤M*Real.exp ((1/2)*‖z‖) := by
    have hh := hgrowth z
    rw [show ‖z‖/2=(1/2:ℝ)*‖z‖ by ring] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (show C≤C+1 by linarith) (Real.exp_pos _).le)
  let B := D+‖c‖/Real.pi+1
  have hB : 0<B := by dsimp [B]; positivity
  have hlinear (N : ℕ) :
      2*(N:ℝ)*blockLogMass≤Real.log M+(‖c‖+16*Real.pi*((N:ℝ)+B))/2-Real.log ‖f c‖ := by
    -- Each chosen signed root is its genuine original index; the rectangular indexing only groups the finite prefix.
    let R := 16*Real.pi*((N:ℝ)+B)
    have hR : 0<R := by dsimp [R]; positivity
    let index := fun p:Bool×(Fin 16×Fin N) => (p.1,(finProdFinEquiv p.2).val)
    let u := fun p:Bool×(Fin 16×Fin N) =>
      if p.1 then (x (finProdFinEquiv p.2).val:ℂ) else -(x (finProdFinEquiv p.2).val:ℂ)
    have hi : Function.Injective index := by
      intro p q he
      have hb := congrArg Prod.fst he
      have hk := congrArg Prod.snd he
      change p.1=q.1 at hb
      change (finProdFinEquiv p.2).val=(finProdFinEquiv q.2).val at hk
      apply Prod.ext hb
      exact finProdFinEquiv.injective (Fin.ext hk)
    have hu : Function.Injective u := (signed_roots_injective hx hp).comp hi
    have hz (p : Bool×(Fin 16×Fin N)) : f (u p)=0 := by
      dsimp [u]
      split
      · exact (hzero _).1
      · exact (hzero _).2
    have hd (p : Bool×(Fin 16×Fin N)) :
        ‖c-u p‖≤(p.2.1.val+1:ℝ)*Real.pi*((N:ℝ)+B) := by
      have hk : ((finProdFinEquiv p.2).val:ℝ)≤(p.2.1.val+1:ℝ)*N := by
        change ((p.2.2.val+N*p.2.1.val:ℕ):ℝ)≤_
        push_cast
        have hh : (p.2.2.val:ℝ)≤N := by exact_mod_cast p.2.2.isLt.le
        nlinarith
      have hnorm : ‖u p‖=x (finProdFinEquiv p.2).val := by
        dsimp [u]
        split <;> simp only [norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp _)]
      have hcp : ‖c‖=Real.pi*(B-D-1) := by dsimp [B]; field_simp; ring
      calc
        ‖c-u p‖ ≤ ‖c‖+x (finProdFinEquiv p.2).val := by rw [← hnorm]; exact norm_sub_le _ _
        _ ≤ ‖c‖+Real.pi*(((finProdFinEquiv p.2).val:ℝ)+D) := add_le_add le_rfl (hbound _)
        _ ≤ Real.pi*((p.2.1.val+1:ℝ)*N+B) := by rw [hcp]; nlinarith [Real.pi_pos]
        _ ≤ _ := by
          have hj : (0:ℝ)≤p.2.1.val := Nat.cast_nonneg _
          have hb := mul_nonneg hj hB.le
          nlinarith [mul_nonneg Real.pi_pos.le hb]
    have hball (p : Bool×(Fin 16×Fin N)) : u p∈closedBall c R := by
      have hj : (p.2.1.val+1:ℝ)≤16 := by exact_mod_cast p.2.1.isLt
      apply mem_closedBall.mpr
      rw [dist_eq_norm']
      exact (hd p).trans (by dsimp [R]; gcongr)
    have hlower (p : Bool×(Fin 16×Fin N)) :
        Real.log (16/(p.2.1.val+1:ℝ))≤Real.log (R*‖c-u p‖⁻¹) := by
      have hne : c≠u p := fun h => hc (h ▸ hz p)
      have hnp : 0<‖c-u p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      have he : 16/(p.2.1.val+1:ℝ)=R/((p.2.1.val+1:ℝ)*Real.pi*((N:ℝ)+B)) := by
        dsimp [R]
        field_simp
      apply Real.log_le_log (by positivity)
      rw [he,← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left hR.le hnp (hd p)
    have hsum := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => hlower p)
    have he : (∑ p:Bool×(Fin 16×Fin N),Real.log (16/(p.2.1.val+1:ℝ)))=
        2*(N:ℝ)*blockLogMass := by
      simp only [Fintype.sum_prod_type,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,
        Fintype.card_fin,Fintype.card_bool]
      simp only [← Finset.mul_sum,blockLogMass]
      ring
    rw [he] at hsum
    exact hsum.trans (by
      have hh := indexed_zero_log_sum_le_exp hf hc hM (by norm_num : (0:ℝ)≤1/2)
        hR hMbound u hu hball hz
      rw [show (1/2:ℝ)*(‖c‖+R)=(‖c‖+R)/2 by ring] at hh
      exact hh)
  have hgap : 0<2*blockLogMass-8*Real.pi := by
    have hpib : Real.pi<13/4 := by linarith [Real.pi_lt_d2]
    linarith [blockLogMass_gt]
  obtain ⟨N,hN⟩ := exists_nat_gt
    ((Real.log M+‖c‖/2+8*Real.pi*B-Real.log ‖f c‖)/(2*blockLogMass-8*Real.pi))
  have hh := (div_lt_iff₀ hgap).mp hN
  nlinarith [hlinear N]

end
end jacobi.Complex
