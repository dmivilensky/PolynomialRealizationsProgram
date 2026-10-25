import polyak.FiniteHorizon.SourcePrefactor
import polyak.Regularity.MemoryCritical

/-!
Article: Appendix C, the actual uniform prefactor at the critical parameter.
Use: the established critical derivative, central source factors and exact
finite-memory rate discharge every input to the constructive price argument.
-/
noncomputable section
namespace polyak.FiniteHorizon
open Growth Growth.FiniteHorizon Spectral Boundary Regularity Filter
open scoped Topology

theorem exists_uniform_prefactor_critical :
    ∃ H : ℕ,7≤H ∧ ∃ C : ℝ,0<C ∧ ∀ n : ℕ,
      envelope 0 (2*Threshold.criticalQ) (Threshold.criticalQ^2) H n≤C := by
  obtain ⟨H,hRate,hH⟩:=(memory_rate_eq_critical.and (eventually_ge_atTop 7)).exists
  have heq : (0 : ℝ)-Real.log Threshold.criticalQ=V 0 := by
    rw [Threshold.log_criticalQ,Threshold.V_zero]
    ring
  have hVT : 0<V 0 := by
    have hl:=Real.log_neg Threshold.criticalQ_pos Threshold.criticalQ_lt_one
    rw [←heq]
    linarith
  have hf : ∀ᶠ t in 𝓝[≥] (0 : ℝ),HasPhysicalFactors7 Threshold.criticalQ t:=
    (eventually_hasPhysicalFactors7_p5 Threshold.criticalQ_pos).filter_mono nhdsWithin_le_nhds
  obtain ⟨C,hC,hbound⟩:=exists_prefactor_of_source_germ Threshold.criticalQ_pos V_hasDerivAt_zero
    (by norm_num : (0 : ℝ)<1) hVT heq hH (by rw [hRate,Real.exp_zero]) hf
  refine ⟨H,hH,C,hC,fun n => ?_⟩
  simpa only [mul_zero,Real.exp_zero,mul_one] using hbound n

end polyak.FiniteHorizon
