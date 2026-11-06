import nesterov.Slow.QueryLimits
import nesterov.IQC.PolynomialSymbols
import nesterov.Phase.SingleAtom
import nesterov.Slow.QueryNormalization

/-! The query-normalized slow coefficients are evaluations of the actual method. -/
namespace nesterov.Slow.SecondOrderFamily
noncomputable section
open Spectral Polynomial
variable {θ y : ℝ} (F : SecondOrderFamily θ y)

theorem sampled_wave (ε c γ : ℝ) :
    polyak.Waves.z (-c*ε) (ε*γ)=F.wave ε (SecondOrderFamily.slowPoint c γ) := by
  unfold polyak.Waves.z SecondOrderFamily.wave SecondOrderFamily.slowPoint
  congr 1
  push_cast
  ring

theorem sampled_query_value {ε c γ : ℝ} (hω : ε*γ∈Set.Icc (0:ℝ) Real.pi) :
    ((F.method ε).symbolPair (ε^2) 1 (-c*ε)).u (Phase.frequency (ε*γ))=
      (F.u ε).eval₂ Complex.ofRealHom (F.wave ε (SecondOrderFamily.slowPoint c γ)) := by
  simp only [StationaryMethod.symbolPair_u,Phase.arccos_frequency hω,F.sampled_wave,Polynomial.eval_map]

theorem sampled_query_ratio {ε c γ : ℝ} (hω : ε*γ∈Set.Icc (0:ℝ) Real.pi)
    (hε : ε^2≠1)
    (hU : (F.u ε).eval₂ Complex.ofRealHom (F.wave ε (SecondOrderFamily.slowPoint c γ))≠0) :
    ((F.method ε).symbolPair (ε^2) 1 (-c*ε)).p (Phase.frequency (ε*γ))/
      ((F.method ε).symbolPair (ε^2) 1 (-c*ε)).u (Phase.frequency (ε*γ))=
      F.queryRatio ε (SecondOrderFamily.slowPoint c γ) := by
  rw [F.sampled_query_value hω]
  simp only [StationaryMethod.symbolPair_p,Phase.arccos_frequency hω,F.sampled_wave]
  rw [(F.method ε).normalizedPolynomial_complex_eval]
  simp only [Polynomial.eval_map]
  unfold SecondOrderFamily.queryRatio SecondOrderFamily.curvature
  change ((((1+ε^2)/(1-ε^2):ℝ):ℂ)*(F.u ε).eval₂ Complex.ofRealHom _-
      ((2/(1-ε^2):ℝ):ℂ)*(F.v ε).eval₂ Complex.ofRealHom _)/
      (F.u ε).eval₂ Complex.ofRealHom _=_
  have hd : (1:ℂ)-(ε:ℂ)^2≠0 := by exact_mod_cast (sub_ne_zero.mpr (Ne.symm hε))
  push_cast
  field_simp [hU,hd]

end
end nesterov.Slow.SecondOrderFamily
