import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Multiset
import Mathlib.Analysis.Asymptotics.Defs

/-!
A bounded-degree root-continuity theorem proved directly from factorization.
It permits loss of degree at the limit. A comparison at a second evaluation
point prevents roots escaping to infinity from destroying local root existence.
-/
namespace nesterov.Slow
noncomputable section
open Polynomial Filter Set
open scoped Topology

private lemma norm_eval_product (p : Polynomial ℂ) (z : ℂ) :
    ‖p.eval z‖=‖p.leadingCoeff‖*(p.roots.map (fun r=>‖z-r‖)).prod := by
  have hprod (s : Multiset ℂ) : ‖s.prod‖=(s.map (fun a=>‖a‖)).prod := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih => simp only [Multiset.prod_cons,norm_mul,Multiset.map_cons,ih]
  rw [(IsAlgClosed.splits p).eval_eq_prod_roots,norm_mul,hprod,Multiset.map_map]
  rfl

lemma norm_eval_le_of_roots_away (p : Polynomial ℂ) {N : ℕ} (hp : p.natDegree≤N)
    (z w : ℂ) {δ : ℝ} (hδ : 0<δ)
    (haway : ∀ r : ℂ,p.eval r=0 → δ≤‖z-r‖) :
    ‖p.eval w‖≤(1+‖w-z‖/δ)^N*‖p.eval z‖ := by
  let C : ℝ := 1+‖w-z‖/δ
  have hC : 1≤C := le_add_of_nonneg_right (div_nonneg (norm_nonneg _) hδ.le)
  have hpoint (r : ℂ) (hr : r∈p.roots) : ‖w-r‖≤C*‖z-r‖ := by
    have hd := haway r ((mem_roots (ne_zero_of_mem_roots hr)).mp hr)
    have hnorm : ‖w-r‖≤‖w-z‖+‖z-r‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (w-z) (z-r)
    have hh := mul_le_mul_of_nonneg_left hd (div_nonneg (norm_nonneg (w-z)) hδ.le)
    have he : ‖w-z‖/δ*δ=‖w-z‖ := div_mul_cancel₀ _ hδ.ne'
    dsimp [C]
    nlinarith
  have hprod := Multiset.prod_map_le_prod_map₀ (s:=p.roots)
    (fun r=>‖w-r‖) (fun r=>C*‖z-r‖) (fun _ _=>norm_nonneg _) hpoint
  rw [Multiset.prod_map_mul,Multiset.map_const',Multiset.prod_replicate] at hprod
  have hpow : C^p.roots.card≤C^N := pow_le_pow_right₀ hC ((card_roots' p).trans hp)
  rw [norm_eval_product,norm_eval_product]
  have hpos : 0≤(p.roots.map (fun r=>‖z-r‖)).prod :=
    Multiset.prod_nonneg (by intro a ha;obtain ⟨r,_,rfl⟩:=Multiset.mem_map.mp ha;exact norm_nonneg _)
  have hh := hprod.trans (mul_le_mul_of_nonneg_right hpow hpos)
  nlinarith [mul_le_mul_of_nonneg_left hh (norm_nonneg p.leadingCoeff)]

/-- Every root of a nonzero polynomial limit is approximated by actual roots
of the varying bounded-degree polynomials; no fixed limit degree is assumed. -/
theorem eventually_exists_root_near {A : Type*} {l : Filter A}
    {p : A→Polynomial ℂ} {p₀ : Polynomial ℂ} {N : ℕ}
    (hdeg : ∀ a,(p a).natDegree≤N)
    (heval : ∀ z : ℂ,Tendsto (fun a=>(p a).eval z) l (𝓝 (p₀.eval z)))
    (hp₀ : p₀≠0) {z : ℂ} (hz : p₀.eval z=0) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ a in l,∃ r : ℂ,(p a).eval r=0 ∧ ‖r-z‖<δ := by
  have hex : ∃ w : ℂ,p₀.eval w≠0 := by
    by_contra! hh
    apply hp₀
    apply Polynomial.funext
    intro x
    simpa using hh x
  obtain ⟨w,hw⟩ := hex
  let C : ℝ := 1+‖w-z‖/δ
  have ht : Tendsto (fun a=>‖(p a).eval w‖-C^N*‖(p a).eval z‖) l
      (𝓝 ‖p₀.eval w‖) := by
    convert ((heval w).norm.sub (tendsto_const_nhds.mul (heval z).norm)) using 1
    rw [hz,norm_zero,mul_zero,sub_zero]
  have hp := ht.eventually (eventually_gt_nhds (norm_pos_iff.mpr hw))
  filter_upwards [hp] with a ha
  by_contra! hn
  have haway (r : ℂ) (hr : (p a).eval r=0) : δ≤‖z-r‖ := by
    simpa only [norm_sub_rev] using hn r hr
  have hb := norm_eval_le_of_roots_away (p a) (hdeg a) z w hδ haway
  change ‖(p a).eval w‖≤C^N*‖(p a).eval z‖ at hb
  linarith

end
end nesterov.Slow
