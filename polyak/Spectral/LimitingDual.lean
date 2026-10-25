import polyak.Spectral.NormalizedCertificate
import polyak.Duality.Separation

/-!
Article: Appendix A, existence of the nonpositive limiting dual symbol.
Use: one fixed compact convex coefficient hull contains every normalized
strict certificate approaching the maximal twist from above.
Proof: actual strict separation, compact subsequences and continuous polynomial evaluation.
-/

namespace polyak.Spectral
noncomputable section
open Set Filter Duality
open scoped Topology

/-- Article: a limiting dual exists at every nonzero-exponent spectral boundary.
Use: no finite active set, multiplier support or nonzero symbol is assumed. -/
theorem exists_limiting_dual {s : ℝ} (hs : 0 < s) :
    ∃ d∈dualHull s hs,d.1=0 ∧
      ∀ c : Frequency,(evaluateDual (Real.sinh (V s)) d (dualAngle s hs c)).re ≤ 0 := by
  classical
  let v : ℕ → ℝ := fun n => V s+((n : ℝ)+1)⁻¹
  let u : ℕ → ℝ := fun n => Real.sinh (v n)
  have hv (n : ℕ) : V s < v n := by
    dsimp [v]
    exact lt_add_of_pos_right _ (inv_pos.mpr (by positivity))
  have hcert (n : ℕ) :
      Nonempty (StrictCertificate (Waves.polyakMultiplier (Real.arsinh (u n))) s) := by
    have hi : ¬ ∃ ν C,Waves.MixtureFeasible ν (Waves.polyakMultiplier (v n)) C s := by
      rintro ⟨ν,C,h⟩
      have hfeas := (Waves.mixtureFeasible_polyak_iff ν (v n) C s).mp h
      exact (not_le.mpr (hv n)) ((isGreatest_V s).2 ⟨ν,C,hfeas⟩)
    simpa only [u,Real.arsinh_sinh] using (infeasible_iff_strictCertificate _ _).mp hi
  have hx (n : ℕ) : ∃ d∈dualHull s hs,d.1=0 ∧
      ∀ c : Frequency,(evaluateDual (u n) d (dualAngle s hs c)).re ≤ 0 := by
    obtain ⟨cert⟩ := hcert n
    exact cert.exists_normalized_dual hs
  choose d hd hcharge hneg using hx
  obtain ⟨D,hD,φ,hφ,hlim⟩ := (isCompact_dualHull s hs).tendsto_subseq hd
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)+1)⁻¹) atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp
        (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp hn
  have hvlim : Tendsto v atTop (𝓝 (V s)) := by
    simpa only [add_zero] using hinv.const_add (V s)
  have hulim : Tendsto u atTop (𝓝 (Real.sinh (V s))) :=
    (Real.continuous_sinh.tendsto (V s)).comp hvlim
  refine ⟨D,hD,?_,fun c => ?_⟩
  · have hcl : IsClosed {d : DualCoefficient s | d.1=0} :=
      isClosed_eq continuous_fst continuous_const
    exact hcl.mem_of_tendsto hlim (Eventually.of_forall (fun n => hcharge (φ n)))
  · have hcont : Continuous (fun p : ℝ × DualCoefficient s =>
        (evaluateDual p.1 p.2 (dualAngle s hs c)).re) :=
      Complex.continuous_re.comp ((continuous_eval_const _).comp (continuous_evaluateDual s))
    have ht := (hcont.tendsto (Real.sinh (V s),D)).comp
      ((hulim.comp hφ.tendsto_atTop).prodMk_nhds hlim)
    exact le_of_tendsto ht (Eventually.of_forall (fun n => hneg (φ n) c))

end
end polyak.Spectral
