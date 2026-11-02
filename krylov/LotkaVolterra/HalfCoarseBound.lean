import krylov.LotkaVolterra.HalfCoarseBarrier

/-!
Article: main_krylov, thm:limit, coarse half-gamma shooting enclosure.
Use: compare the actual global separating graph with a rational polynomial
barrier and obtain sqrt(sigma(1))<=333/250.  This supplies only the modest
precision required for the retained kappa>=1600 comparison.
Source: the proved analytic saddle chord and actual first-contact comparison.
-/

namespace krylov.LotkaVolterra
noncomputable section
open Set Filter
open scoped Topology

namespace SubcriticalGraph
variable (G : SubcriticalGraph (1 / 2))

/-- The actual half-gamma graph has a saddle tangent strictly above the
rational slope used by the coarse barrier. -/
theorem half_saddle_derivative :
    ∃ r > (87 / 250 : ℝ), HasDerivAt G.σ r 4 := by
  obtain ⟨r, w, hr, hroot, hw₀, hwA, _, hwd⟩ := exists_analytic_saddle_chord
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have heq := G.rawChord_eq_analytic_chord (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
    (fun u hu ↦ ⟨(hwd u hu).1.1.le, (hwd u hu).1.2.le⟩)
    (fun u hu ↦ (hwd u hu).2)
  have hr' : (87 / 250 : ℝ) < r := by
    have hn : (1 : ℝ) - r ≠ 0 := by linarith [hr.2]
    norm_num [saddleSlopeRate, saddleU, saddleS] at hroot
    field_simp [hn] at hroot
    by_contra! hle
    have hh : 0 ≤ ((87 / 250 : ℝ) - r) * (10 - 4 * (87 / 250 : ℝ) - 4 * r) :=
      mul_nonneg (by linarith) (by linarith [hr.2])
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
  exact ⟨r, hr', hF.congr_of_eventuallyEq hnear⟩

/-- Just to the left of the saddle the true graph is strictly below
the rational barrier, by their proved distinct saddle derivatives. -/
theorem half_coarse_barrier_near_saddle :
    ∀ᶠ U : ℝ in 𝓝[<] 4, G.σ U < halfCoarseBarrier U := by
  obtain ⟨r, hr, hd⟩ := G.half_saddle_derivative
  have hbd : halfCoarseBarrierDerivative 4 = (87 / 250 : ℝ) := by
    norm_num [halfCoarseBarrierDerivative]
  have hh := hd.sub (halfCoarseBarrier_hasDerivAt 4)
  rw [hbd] at hh
  have hs : G.σ 4 = 3 := by
    have hh := G.saddle
    norm_num [saddleU, saddleS] at hh
    exact hh
  have hp := ((hasDerivAt_iff_tendsto_slope_left_right.mp hh).1).eventually
    (Ioi_mem_nhds (sub_pos.mpr hr))
  filter_upwards [hp, self_mem_nhdsWithin] with U hU hU4
  change U < 4 at hU4
  rw [slope_def_field] at hU
  dsimp only [Pi.sub_apply] at hU
  rw [hs, halfCoarseBarrier_four, sub_self, sub_zero] at hU
  have hneg : G.σ U - halfCoarseBarrier U < 0 :=
    ((div_pos_iff.mp hU).resolve_left (fun h ↦ (not_lt_of_ge (by linarith : U - 4 ≤ 0)) h.2)).1
  linarith

/-- The rational polynomial is an actual strict upper barrier for the
entire required half-gamma graph segment, proved by first contact. -/
theorem half_lt_coarse_barrier {U : ℝ} (hU : U ∈ Ico (1 : ℝ) 4) :
    G.σ U < halfCoarseBarrier U := by
  have hright : ∀ᶠ V : ℝ in 𝓝[<] 4, U < V :=
    nhdsWithin_le_nhds (Ioi_mem_nhds hU.2)
  obtain ⟨V, hGV, hUV, hV4⟩ :=
    (G.half_coarse_barrier_near_saddle.and (hright.and self_mem_nhdsWithin)).exists
  let f : ℝ → ℝ := fun t ↦ halfCoarseBarrier (-t) - G.σ (-t)
  let f' : ℝ → ℝ := fun t ↦
    2 * G.σ (-t) * (G.σ (-t) - 1 - (-t) / 2) /
      ((-t) * (G.σ (-t) + 1 - (-t))) - halfCoarseBarrierDerivative (-t)
  have hdom (t : ℝ) (ht : t ∈ Icc (-V) (-U)) : -t ∈ Ico (1 : ℝ) 4 :=
    ⟨by linarith [ht.2, hU.1], by linarith [ht.1, hV4]⟩
  have hfd (t : ℝ) (ht : t ∈ Icc (-V) (-U)) : HasDerivAt f (f' t) t := by
    have hx := hdom t ht
    have hG := G.derivative (-t) (by linarith [hx.1]) (by norm_num [saddleU]; linarith [hx.2])
    have hh := ((halfCoarseBarrier_hasDerivAt (-t)).comp t (hasDerivAt_id t).neg).sub
      (hG.comp t (hasDerivAt_id t).neg)
    convert hh using 1
    · rfl
    · dsimp only [f']
      ring_nf
  have hfin (t : ℝ) (ht : t ∈ Icc (-V) (-U)) (hf : f t = 0) (_ : 0 ≤ (1 : ℝ)) : 0 < f' t := by
    have hx := hdom t ht
    have he : halfCoarseBarrier (-t) = G.σ (-t) := sub_eq_zero.mp hf
    have hb := halfCoarseBarrier_residual ⟨hx.1, hx.2.le⟩ hx.2
    rw [he] at hb
    have hg := (G.lower (-t) ⟨by linarith [hx.1], by norm_num [saddleU]; exact hx.2⟩).2.2
    have hd : 0 < (-t) * (G.σ (-t) + 1 - (-t)) := mul_pos (by linarith [hx.1]) (by linarith)
    apply sub_pos.mpr
    apply (lt_div_iff₀ hd).mpr
    nlinarith
  have hh := pair_positive_invariant (by linarith : -V ≤ -U) hfd
    (fun t _ ↦ hasDerivAt_const t (1 : ℝ)) (by simpa only [f, neg_neg] using sub_pos.mpr hGV)
    (by norm_num : (0 : ℝ) < 1) hfin (by intro t ht h; norm_num at h)
  simpa only [f, neg_neg, sub_pos] using hh.1

/-- A modest rigorous enclosure of the actual half-gamma crossing. -/
theorem half_crossing_lt : G.σ 1 < (221578863 / 125000000 : ℝ) := by
  simpa only [halfCoarseBarrier_one] using G.half_lt_coarse_barrier (by norm_num : (1 : ℝ) ∈ Ico 1 4)

/-- The actual optimal half-gamma constant needs only this four-decimal
upper bound for the retained Chebyshev comparison. -/
theorem half_crossing_sqrt_le : Real.sqrt (G.σ 1) ≤ (333 / 250 : ℝ) := by
  apply Real.sqrt_le_iff.mpr
  exact ⟨by norm_num, by linarith [G.half_crossing_lt]⟩

end SubcriticalGraph
end
end krylov.LotkaVolterra
