import jacobi.Support.SineProductLimit
import jacobi.Jacobi.CorrectedDistance

/-!
Article: jacobi, Appendix C.3 (top-node polynomials).
The genuine arbitrary-shift sine-product limit is transferred from its
actual nonintegral frequency to the article's exact degree normalization
and mesh coordinate. The fixed endpoint parameters are arbitrary.
Use: support_sineProduct_uniform proves the full compact-uniform source statement and top-node normalization reuses this exact original degree scale.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter
open scoped Topology

/-- The original support sine products have precisely the article's normalized moving-index limit, at the original degree and mesh scale.
Use: support_sineProduct_uniform proves the full compact-uniform source statement and top-node normalization reuses this exact original degree scale.
Article: jacobi, Appendix C.3 (sine-product estimates).
Proof: the actual original affine frequency divided by its degree tends to one. This transfers the genuine moving mesh ratio and the proved arbitrary-frequency sine-product limit; the same positive real-power ratio transfers its normalization exactly. -/
theorem support_sineProduct_limit (a b : ℝ) {ι : Type*} {l : Filter ι} {n m : ι→ℕ}
    {s t : ℝ} (hs:0<s) (ht:t∈Ioo (0:ℝ) 1) (hn:Tendsto n l atTop)
    (hm:Tendsto (fun i => (m i:ℝ)/(n i:ℝ)) l (𝓝 t)) :
    Tendsto (fun i => (n i:ℝ)^(1-s)*sineProduct (step a b (n i)) s (m i)) l
      (𝓝 ((Gamma s)⁻¹*(sin (π*t)/π)^(s-1))) := by
  -- Both degree changes are exact positive scalar identities before their limits are evaluated.
  have hN := (jacobi.Jacobi.frequency_tendsto a b).comp hn
  have hratio := (jacobi.Jacobi.frequency_ratio_tendsto a b).comp hn
  have hmesh : Tendsto (fun i => (m i:ℝ)/ jacobi.Jacobi.frequency a b (n i)) l (𝓝 t) := by
    have h := hm.div hratio one_ne_zero
    simp only [div_one] at h
    apply (tendsto_congr' ?_).mpr h
    filter_upwards [hn.eventually (eventually_gt_atTop (0:ℕ))] with i hi
    have hni : (n i:ℝ)≠0 := by exact_mod_cast hi.ne'
    dsimp [Function.comp_def]
    field_simp [hni]
  have hp := sineProduct_limit hs ht hN hmesh
  have hi := hratio.inv₀ one_ne_zero
  simp only [inv_one] at hi
  have hc := hi.rpow_const (p:=1-s) (Or.inl one_ne_zero)
  simp only [one_rpow] at hc
  have hlim := hc.mul hp
  simp only [one_mul] at hlim
  apply (tendsto_congr' ?_).mpr hlim
  filter_upwards [hn.eventually (eventually_gt_atTop (0:ℕ)),
    hN.eventually (eventually_gt_atTop (0:ℝ))] with i hni hNi
  have hniR : (0:ℝ)<n i := by exact_mod_cast hni
  change 0< jacobi.Jacobi.frequency a b (n i) at hNi
  dsimp [Function.comp_def,step]
  rw [inv_div,Real.div_rpow hniR.le hNi.le]
  field_simp [(Real.rpow_pos_of_pos hNi (1-s)).ne']

end
end jacobi.Support
