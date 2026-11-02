import krylov.Functions.PlanarSourceShrink
import krylov.Functions.PlanarAttainedChord
import krylov.Functions.ReferenceFibreNormalization

/-!
Article: main_krylov, prop:Fcycle(iii), sharp actual self-concordant sources.
Use: choose one attained extremal data chord, shrink BOTH true scalar cubics
by the same factor and retain the sharp cubic lower coefficient for every
unrestricted common output. The true minima, Hessian metric, exact canonical
tensor budget and complete printed self-concordance ball are conclusions.
Source: the genuine all-output function lower bound, attained binary chord,
exact tensor scaling and actual true-minimizer shrink construction.
-/
namespace krylov.Functions
noncomputable section
open Set krylov.Tensor.BinaryCubic
open scoped InnerProductSpace

/-- The exact all-chord minimax is strictly positive at every finite ratio.
Article: main_krylov, prop:Fcycle(iii), a nontrivial attained information fibre.
Source: the reversible shear estimate and the sharp value M_F(0)=1/3. -/
theorem binaryFibreMinimax_pos (r : ℝ) : 0<fibreMinimax r := by
  have hs := fibreMinimax_shear 0 r
  rw [fibreMinimax_zero] at hs
  have hn := (fibreMinimax_bounds r).1
  by_contra hh
  have hz : fibreMinimax r=0 := by linarith
  rw [hz,mul_zero] at hs
  norm_num at hs

/-- A positive actual tensor rescaling preserves the genuine finite-scale
all-output lower bound with its exact squared amplitude.
Article: main_krylov, prop:Fcycle(iii). -/
theorem planeCubic_scaled_all_output_lower (r : ℝ) (t u : krylov.Tensor.BinaryCubic)
    (hobs : observe r t=observe r u) (hd : u.t2-t.t2≠0) (hr : r≠0) :
    ∃ C : ℝ, 0<C ∧ ∀ p α : ℝ, 0<p → 0<α → α*p≤1 → ∀ x : Plane,
      α^2*(r^2/4*chordValue r t u*Real.sqrt (1+4*r^2))*p^3-C*α^3*p^4≤
        max ‖gradient (planeCubicObjective p r (scaleBinaryCubic α t)) x‖
          ‖gradient (planeCubicObjective p r (scaleBinaryCubic α u)) x‖ := by
  obtain ⟨C,hC,hlower⟩ := planeCubic_all_output_chord_lower r t u hobs hd hr
  refine ⟨C,hC,?_⟩
  intro p α hp hα hαp x
  have hh := mul_le_mul_of_nonneg_left (hlower (α*p) (mul_pos hα hp) hαp (α • x)) (inv_nonneg.mpr hα.le)
  rw [planeCubicGradient_tensor_scale p r α hα.ne',planeCubicGradient_tensor_scale p r α hα.ne',
    norm_smul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hα.le),←mul_max_of_nonneg _ _ (inv_nonneg.mpr hα.le)]
  exact hh.trans' (by field_simp; ring_nf; exact le_refl _)

set_option maxHeartbeats 800000 in
/-- The sharp attained information fibre consists of genuine self-concordant
functions with actual true minima and the exact prescribed canonical budget.
Its common-output lower bound has the printed leading coefficient and one
uniform fourth-order loss. Article: main_krylov, prop:Fcycle(iii).
Constants and the two source tensors are chosen before the cycle radius or
an arbitrary method's common returned point. -/
theorem planeCubic_sharp_true_metric_sources (r a : ℝ) (hr : 0<r) (ha : 0<a) (ha₁ : a<1) :
    ∃ t u : krylov.Tensor.BinaryCubic, Chord r t u ∧ chordValue r t u=fibreMinimax r ∧
    ∃ ε₀ C M E : ℝ, 0<ε₀ ∧ 0<C ∧ 0<M ∧ 0<E ∧
      ∀ p : ℝ, 0<p → p<ε₀ → let α := 2*a*(1-C*p)^3
      0<α ∧ α≤2*a ∧ observe r (scaleBinaryCubic α t)=observe r (scaleBinaryCubic α u) ∧
      ∃ x y : Plane,
        ‖x-planeOfPair (p,r*p)‖≤M*p^2 ∧ ‖y-planeOfPair (p,r*p)‖≤M*p^2 ∧
        ‖planeCubicHessian p r (scaleBinaryCubic α t) x-ContinuousLinearMap.id ℝ Plane‖≤C*p ∧
        ‖planeCubicHessian p r (scaleBinaryCubic α u) y-ContinuousLinearMap.id ℝ Plane‖≤C*p ∧
        PlanarTrueMetricRealization p r a α t x ∧ PlanarTrueMetricRealization p r a α u y ∧
        ∀ z : Plane,
          a^2*r^2*Real.sqrt (1+4*r^2)*fibreMinimax r*p^3-E*p^4≤
          max ‖gradient (planeCubicObjective p r (scaleBinaryCubic α t)) z‖
            ‖gradient (planeCubicObjective p r (scaleBinaryCubic α u)) z‖ := by
  obtain ⟨t,u,hch,hatt⟩ := exists_chord_attaining_fibreMinimax r
  have hv : 0<chordValue r t u := hatt ▸ binaryFibreMinimax_pos r
  have hd : u.t2-t.t2≠0 := by
    intro he
    have hsame : t.t2-u.t2=0 := by linarith only [he]
    unfold chordValue at hv
    rw [hsame,abs_zero,mul_zero,zero_div] at hv
    exact lt_irrefl _ hv
  obtain ⟨ep,C,M,hep,hC,hM,hsource⟩ := planeCubic_pair_true_metric_realization r a ha ha₁ hch.1 hch.2.1
  obtain ⟨Cl,hCl,hlower⟩ := planeCubic_scaled_all_output_lower r t u (chord_observations hch) hd hr.ne'
  let K := r^2/4*fibreMinimax r*Real.sqrt (1+4*r^2)
  have hMF := binaryFibreMinimax_pos r
  have hK : 0<K := by dsimp only [K]; positivity
  let E := 24*a^2*K*C+8*Cl*a^3+1
  refine ⟨t,u,hch,hatt,min ep (min (1/(2*a+1)) (1/(C+1))),C,M,E,by positivity,hC,hM,
    by dsimp only [E]; positivity,?_⟩
  intro p hp he
  obtain ⟨hα,hαU,x,y,hx,hy,hHx,hHy,ht,hu⟩ := hsource p hp (he.trans_le (min_le_left _ _))
  let q := 1-C*p
  let α := 2*a*q^3
  have hq : 0<q := by
    have hh := (lt_div_iff₀ (by positivity : 0<C+1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    dsimp only [q]
    nlinarith only [hh,hp]
  have hαp : α*p≤1 := by
    have hh := (lt_div_iff₀ (by positivity : 0<2*a+1)).mp
      (he.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith only [mul_le_mul_of_nonneg_right hαU hp.le,hh,hp]
  have hobs : observe r (scaleBinaryCubic α t)=observe r (scaleBinaryCubic α u) := by
    have ho := chord_observations hch
    have h0 := congrArg Observation.t0 ho
    have hP := congrArg Observation.P ho
    have hD := congrArg Observation.t3 ho
    dsimp only [observe,scaleBinaryCubic] at *
    congr 1 <;> nlinarith
  refine ⟨hα,hαU,hobs,x,y,hx,hy,hHx,hHy,ht,hu,?_⟩
  intro z
  have hb := hlower p α hp hα hαp z
  rw [hatt] at hb
  have hq6 : 1-6*C*p≤q^6 := by
    have hh := one_add_mul_sub_le_pow (show -1≤q by linarith) 6
    norm_num only [Nat.cast_ofNat] at hh
    dsimp only [q] at *
    nlinarith only [hh]
  have hα2 : 4*a^2*(1-6*C*p)≤α^2 := by
    have hh := mul_le_mul_of_nonneg_left hq6 (by positivity : 0≤4*a^2)
    dsimp only [α]
    nlinarith only [hh]
  have hα3 : α^3≤8*a^3 := (pow_le_pow_left₀ hα.le hαU 3).trans_eq (by ring)
  have hmain := mul_le_mul_of_nonneg_right hα2 (mul_nonneg hK.le (pow_nonneg hp.le 3))
  have herr := mul_le_mul_of_nonneg_left hα3 (mul_nonneg hCl.le (pow_nonneg hp.le 4))
  apply le_trans ?_ hb
  change _ ≤ α^2*K*p^3-Cl*α^3*p^4
  dsimp only [K,E] at *
  nlinarith only [hmain,herr,pow_pos hp 4]

end
end krylov.Functions
