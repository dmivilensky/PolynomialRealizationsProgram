import krylov.LotkaVolterra.HalfCoarseBound

/-!
Article: main_krylov, apC:prop:digits, comparison calculus for exact certificates.
Source: first-contact comparison at a strict rational differential barrier.
The saddle derivative is the actual derivative of the constructed separating
curve, obtained from its proved analytic saddle chart.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open scoped Topology

namespace SubcriticalGraph
variable (G : SubcriticalGraph (1 / 2))

/-- The actual saddle derivative, including its exact quadratic equation. -/
theorem half_saddle_derivative_exact :
    ∃ r ∈ Ioo (0 : ℝ) (1/2), 4*r^2-10*r+3=0 ∧ HasDerivAt G.σ r 4 := by
  obtain ⟨r, w, hr, hroot, hw₀, hwA, _, hwd⟩ := exists_analytic_saddle_chord
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have heq := G.rawChord_eq_analytic_chord (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
    (fun u hu ↦ ⟨(hwd u hu).1.1.le, (hwd u hu).1.2.le⟩)
    (fun u hu ↦ (hwd u hu).2)
  have hpoly : 4*r^2-10*r+3=0 := by
    have hn : (1 : ℝ) - r ≠ 0 := by linarith [hr.2]
    norm_num [saddleSlopeRate, saddleU, saddleS] at hroot
    field_simp [hn] at hroot
    nlinarith
  let T : ℝ → ℝ := fun U ↦ (4 - U) / 2
  let F : ℝ → ℝ := fun U ↦ 3 - (4 - U) * w (T U)
  have hT : HasDerivAt T (-(1 / 2)) 4 := by
    convert ((hasDerivAt_id (4 : ℝ)).const_sub 4).div_const 2 using 1 <;> norm_num [T]
  have hwD : HasDerivAt w (deriv w 0) (T 4) := by
    simpa only [T, sub_self, zero_div] using hwA.differentiableAt.hasDerivAt
  have hwT := hwD.comp 4 hT
  have hF : HasDerivAt F r 4 := by
    convert (((hasDerivAt_id (4 : ℝ)).const_sub 4).mul hwT).const_sub 3 using 1
    · rfl
    · change r = -(-1 * w (T 4) + (4 - 4) * (deriv w 0 * -(1 / 2)))
      norm_num [T, hw₀]
  have hnear : G.σ =ᶠ[𝓝 (4 : ℝ)] F := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (2 : ℝ) < 4) (by norm_num : (4 : ℝ) < 6)] with U hU
    by_cases hUF : U = 4
    · subst U
      have hs := G.saddle
      norm_num [saddleU, saddleS] at hs
      simp only [F, sub_self, zero_mul, sub_zero]
      exact hs
    · have hu : T U ∈ Icc (-1 : ℝ) 1 := by dsimp [T]; constructor <;> linarith [hU.1, hU.2]
      have hu₀ : T U ≠ 0 := by dsimp [T]; exact div_ne_zero (sub_ne_zero.mpr (Ne.symm hUF)) (by norm_num)
      have hh := heq (T U) hu hu₀
      dsimp only [rawChord] at hh
      norm_num [saddleU, saddleS] at hh
      change (3 - G.σ (4 - 2 * T U)) / (2 * T U) = w (T U) at hh
      have ht : 2 * T U = 4 - U := by dsimp [T]; ring
      rw [ht, show 4 - (4 - U) = U by ring] at hh
      have hm := (div_eq_iff (sub_ne_zero.mpr (Ne.symm hUF))).mp hh
      change G.σ U = 3 - (4 - U) * w (T U)
      nlinarith
  exact ⟨r, hr, hpoly, hF.congr_of_eventuallyEq hnear⟩

/-- Coarse rational root isolation sufficient to orient both certified barriers. -/
theorem half_saddle_root_bounds {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) (1/2))
    (hpoly : 4*r^2-10*r+3=0) :
    r ∈ Ioo (34861217/100000000 : ℝ) (34861220/100000000 : ℝ) := by
  constructor
  · by_contra! hn
    have hh := mul_nonneg (show 0 ≤ (34861217/100000000 : ℝ)-r by linarith)
      (show 0 ≤ 10-4*(34861217/100000000 : ℝ)-4*r by linarith [hr.2])
    nlinarith
  · by_contra! hn
    have hh := mul_nonneg (show 0 ≤ r-(34861220/100000000 : ℝ) by linarith)
      (show 0 ≤ 10-4*r-4*(34861220/100000000 : ℝ) by linarith [hr.2])
    nlinarith

/-- A signed strict differential barrier controls the whole half-gamma
branch. Both sides use the same first-contact theorem and the actual saddle
limit; no numerical trajectory is assumed. -/
theorem half_signed_barrier {b b' : ℝ → ℝ} {sign : ℝ}
    (hsign : sign^2 = 1) (hb4 : b 4 = 3)
    (hbd : ∀ U, HasDerivAt b (b' U) U)
    (htangent : ∀ r ∈ Ioo (0 : ℝ) (1/2), 4*r^2-10*r+3=0 → 0 < sign*(r-b' 4))
    (hres : ∀ U ∈ Ico (1 : ℝ) 4,
      sign*(U*b' U*(b U+1-U)-2*b U*(b U-1-U/2)) < 0)
    {U : ℝ} (hU : U ∈ Ico (1 : ℝ) 4) :
    0 < sign*(b U-G.σ U) := by
  have hsne : sign ≠ 0 := by intro hz; simp [hz] at hsign
  obtain ⟨r, hr, hpoly, hd⟩ := G.half_saddle_derivative_exact
  have hh := (hd.sub (hbd 4)).const_mul sign
  have hs : G.σ 4 = 3 := by
    have hx := G.saddle
    norm_num [saddleU, saddleS] at hx
    exact hx
  have hp := ((hasDerivAt_iff_tendsto_slope_left_right.mp hh).1).eventually
    (Ioi_mem_nhds (htangent r hr hpoly))
  have hnear : ∀ᶠ V : ℝ in 𝓝[<] 4, 0 < sign*(b V-G.σ V) := by
    filter_upwards [hp, self_mem_nhdsWithin] with V hV hV4
    change V < 4 at hV4
    rw [slope_def_field] at hV
    dsimp only [Pi.sub_apply] at hV
    rw [hs, hb4, sub_self, mul_zero, sub_zero] at hV
    have hneg : sign*(G.σ V-b V) < 0 :=
      ((div_pos_iff.mp hV).resolve_left (fun h ↦ (not_lt_of_ge (by linarith : V-4 ≤ 0)) h.2)).1
    nlinarith
  have hright : ∀ᶠ V : ℝ in 𝓝[<] 4, U < V :=
    nhdsWithin_le_nhds (Ioi_mem_nhds hU.2)
  obtain ⟨V, hGV, hUV, hV4⟩ :=
    (hnear.and (hright.and self_mem_nhdsWithin)).exists
  let f : ℝ → ℝ := fun t ↦ sign*(b (-t)-G.σ (-t))
  let f' : ℝ → ℝ := fun t ↦ sign*(
    2*G.σ (-t)*(G.σ (-t)-1-(-t)/2)/
      ((-t)*(G.σ (-t)+1-(-t)))-b' (-t))
  have hdom (t : ℝ) (ht : t ∈ Icc (-V) (-U)) : -t ∈ Ico (1 : ℝ) 4 :=
    ⟨by linarith [ht.2, hU.1], by linarith [ht.1, hV4]⟩
  have hfd (t : ℝ) (ht : t ∈ Icc (-V) (-U)) : HasDerivAt f (f' t) t := by
    have hx := hdom t ht
    have hG := G.derivative (-t) (by linarith [hx.1]) (by norm_num [saddleU]; linarith [hx.2])
    have hx := (((hbd (-t)).comp t (hasDerivAt_id t).neg).sub
      (hG.comp t (hasDerivAt_id t).neg)).const_mul sign
    convert hx using 1
    · rfl
    · dsimp only [f']
      ring_nf
  have hfin (t : ℝ) (ht : t ∈ Icc (-V) (-U)) (hf : f t = 0) (_ : 0 ≤ (1 : ℝ)) : 0 < f' t := by
    have hx := hdom t ht
    have he : b (-t) = G.σ (-t) := by
      have hh : b (-t)-G.σ (-t)=0 := (mul_eq_zero.mp hf).resolve_left hsne
      exact sub_eq_zero.mp hh
    have hb := hres (-t) hx
    rw [he] at hb
    have hg := (G.lower (-t) ⟨by linarith [hx.1], by norm_num [saddleU]; exact hx.2⟩).2.2
    have hd : 0 < (-t)*(G.σ (-t)+1-(-t)) := mul_pos (by linarith [hx.1]) (by linarith)
    have heq : f' t = -(sign*((-t)*b' (-t)*(G.σ (-t)+1-(-t))-
        2*G.σ (-t)*(G.σ (-t)-1-(-t)/2)))/
        ((-t)*(G.σ (-t)+1-(-t))) := by
      dsimp [f']
      rw [div_sub' (ne_of_gt hd)]
      ring
    rw [heq]
    exact div_pos (by linarith) hd
  have hh := pair_positive_invariant (by linarith : -V ≤ -U) hfd
    (fun t _ ↦ hasDerivAt_const t (1 : ℝ)) (by simpa only [f, neg_neg] using hGV)
    (by norm_num : (0 : ℝ) < 1) hfin (by intro t ht h; norm_num at h)
  simpa only [f, neg_neg] using hh.1

end SubcriticalGraph
end
end krylov.LotkaVolterra
