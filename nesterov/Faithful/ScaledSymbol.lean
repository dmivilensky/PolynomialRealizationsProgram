import nesterov.Faithful.FamilyPolynomial
import nesterov.Slow.ScaledLimit

/-! The exact cubic slow symbol along every fixed slow-frequency ray. -/
namespace nesterov.Faithful
noncomputable section
open Polynomial Filter Set
open scoped Topology
variable {θ y : ℝ} (F : Slow.SecondOrderFamily θ y)

theorem div_ofReal_re (z : ℂ) (e : ℝ) : (z/(e:ℂ)).re=z.re/e := by
  rw [div_eq_mul_inv,←Complex.ofReal_inv]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,div_eq_mul_inv]

theorem wave_circle_eq (c γ ε : ℝ) :
    polyak.Waves.z (-c*ε) (ε*γ)=F.wave ε ((c:ℂ)-Complex.I*γ) := by
  unfold polyak.Waves.z Slow.SecondOrderFamily.wave
  congr 1
  push_cast
  ring

theorem scaled_symbol_tendsto (c γ : ℝ) :
    Tendsto (fun ε : ℝ=>familySymbol F c ε (ε*γ)/ε^3) (𝓝[>] (0:ℝ))
      (𝓝 ((c*Flow.delta θ y c+(θ-3*c)*γ^2)/y)) := by
  let w : ℂ := (c:ℂ)-Complex.I*γ
  let z (ε : ℝ) := F.wave ε w
  let U (ε : ℝ) := (F.u ε).eval₂ Complex.ofRealHom (z ε)
  let V (ε : ℝ) := (F.v ε).eval₂ Complex.ofRealHom (z ε)
  let E (ε : ℝ) := Slow.expIncrement (-(ε:ℂ)*w)
  have he : Tendsto (fun ε : ℝ=>ε) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := tendsto_id
  have hε : Tendsto (fun ε : ℝ=>(ε:ℂ)) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).ofReal
  have hU : Tendsto U (𝓝[>] (0:ℝ)) (𝓝 1) := F.query_wave_tendsto he tendsto_const_nhds
  have hz : Tendsto z (𝓝[>] (0:ℝ)) (𝓝 1) := F.wave_tendsto he tendsto_const_nhds
  have hV0 : (F.v 0).eval₂ Complex.ofRealHom 1=0 := by
    rw [←map_one Complex.ofRealHom,eval₂_at_apply,F.v_one,map_zero]
  have hV : Tendsto V (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [hV0] using F.v_eval_tendsto hz
  have hE : Tendsto E (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have hh : Tendsto (fun ε : ℝ=> -(ε:ℂ)*w) (𝓝[>] (0:ℝ)) (𝓝 0) := by simpa using hε.neg.mul_const w
    simpa only [E,Function.comp_def,Slow.expIncrement_zero] using Slow.expIncrement_continuousAt.tendsto.comp hh
  have hcur := F.scaledCurvature_tendsto he (w:=fun _=>w) tendsto_const_nhds
  have hw : Tendsto (fun _ : ℝ=>w) (𝓝[>] (0:ℝ)) (𝓝 w) := tendsto_const_nhds
  have h1 : Tendsto (fun _ : ℝ=>(1:ℂ)) (𝓝[>] (0:ℝ)) (𝓝 1) := tendsto_const_nhds
  have hcomplex := (((hw.mul hE).mul hU).mul (h1.sub hcur)).mul (hU.sub hV).star
  have hmain := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  have hEq : (fun ε : ℝ=>familySymbol F c ε (ε*γ)/ε^3)=ᶠ[𝓝[>] (0:ℝ)]
      (fun ε=>(w*E ε*U ε*(1-F.scaledCurvature ε w)*star (U ε-V ε)).re) := by
    have hUne : ∀ᶠ ε in 𝓝[>] (0:ℝ),U ε≠0 := hU.eventually (isOpen_compl_singleton.mem_nhds (by norm_num : (1:ℂ)≠0))
    filter_upwards [hUne,self_mem_nhdsWithin] with ε hUn hεp
    have hen : (ε:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hεp)
    have hzinc : 1-z ε=(ε:ℂ)*w*E ε := by
      have hh := Slow.expIncrement_mul (-(ε:ℂ)*w)
      change -(ε:ℂ)*w*E ε=z ε-1 at hh
      linear_combination hh
    have hc : ((1-z ε)*(V ε-(ε:ℂ)^2*U ε)*star (V ε-U ε))/(ε:ℂ)^3=
        w*E ε*U ε*(1-F.scaledCurvature ε w)*star (U ε-V ε) := by
      rw [hzinc]
      unfold Slow.SecondOrderFamily.scaledCurvature Slow.SecondOrderFamily.curvature
      change _=w*E ε*U ε*(1-(V ε/U ε)/(ε:ℂ)^2)*star (U ε-V ε)
      rw [show V ε-U ε= -(U ε-V ε) by ring,star_neg]
      field_simp [hen,hUn]
      ring
    have hh := congrArg Complex.re hc
    simp only [←Complex.ofReal_pow,div_ofReal_re] at hh
    convert! hh using 1
    unfold familySymbol
    rw [wave_circle_eq]
    simp only [StationaryMethod.characteristic_eq_polynomial_eval,eval_sub,eval_mul,eval_C,
      Complex.ofReal_one,one_mul,Polynomial.eval_map]
    rfl
  convert! hmain.congr' hEq.symm using 1
  congr 1
  simp only [mul_one,sub_zero,star_one]
  dsimp [w,Flow.delta]
  simp only [Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,
    Complex.div_re,Complex.div_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.normSq_ofReal,Complex.one_re,Complex.one_im]
  field_simp [F.step_pos.ne']
  ring

end
end nesterov.Faithful
