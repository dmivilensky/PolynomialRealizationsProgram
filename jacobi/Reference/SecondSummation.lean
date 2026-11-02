import jacobi.Reference.EulerIntegral
import jacobi.Reference.SecondSummationIntegral
import jacobi.Reference.BetaNormalization
import jacobi.Reference.WaveAnalytic

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Gauss's second summation formula is proved for the actual community
hypergeometric function, with arbitrary complex frequency. Euler's
genuine beta integral first proves the formula on a real interval;
the identity theorem extends it to every frequency, including zeros of
the reciprocal Gamma factors and terminating hypergeometric cases.
Source: Gauss's second summation theorem, DLMF 15.4.28.
Use: establishes equality on an actual real interval before analytic continuation in second_summation.
-/
namespace jacobi.Reference.Hypergeometric
noncomputable section
open Real Set MeasureTheory _root_.Complex
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The real-parameter second summation formula has exactly its printed Gamma normalization.
Use: establishes equality on an actual real interval before analytic continuation in second_summation.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: Gauss's second summation theorem, DLMF 15.4.28.
Proof: Euler's integral and the two proved monotone substitutions
evaluate the actual hypergeometric integral. Legendre duplication
then cancels its original beta normalization, with all Gamma
denominators strictly positive in this real parameter range. -/
theorem second_summation_real {b d : ℝ} (hb : 0<b) (hd : 0<d) :
    ordinaryHypergeometric ((b+2*d-1:ℝ):ℂ) (b:ℂ) ((b+d:ℝ):ℂ) (1/2:ℂ)=
      ((Real.sqrt Real.pi*Real.Gamma (b+d)/
        (Real.Gamma (b/2+d)*Real.Gamma ((b+1)/2)):ℝ):ℂ) := by
  -- Euler's original complex power is the genuine real power on the positive integration bases.
  have he := euler_integral ((b+2*d-1:ℝ):ℂ) hb hd
    (z := (1/2:ℂ)) (by norm_num)
  have hi : (∫ u in (0:ℝ)..1,(jacobi.Jacobi.weight (b-1) (d-1) u:ℂ)*
      (1-(1/2:ℂ)*(u:ℂ))^(-((b+2*d-1:ℝ):ℂ)))=
      ((∫ u in (0:ℝ)..1,jacobi.Jacobi.weight (b-1) (d-1) u*(1-u/2)^(-(b+2*d-1)):ℝ):ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro u hu
    dsimp only
    have hp : 0≤1-u/2 := by linarith [hu.2]
    rw [Complex.ofReal_mul,Complex.ofReal_cpow hp]
    push_cast
    congr 2
    ring
  rw [hi,second_summation_integral hb hd] at he
  have hbn := (Real.Gamma_pos_of_pos hb).ne'
  have hdn := (Real.Gamma_pos_of_pos hd).ne'
  have hbdn := (Real.Gamma_pos_of_pos (add_pos hb hd)).ne'
  have hhalf := (Real.Gamma_pos_of_pos (show 0<b/2+d by linarith)).ne'
  have hother := (Real.Gamma_pos_of_pos (show 0<(b+1)/2 by linarith)).ne'
  have hdup : Real.Gamma b*Real.sqrt Real.pi=
      (2:ℝ)^(b-1)*Real.Gamma (b/2)*Real.Gamma ((b+1)/2) := by
    have hh := Real.Gamma_mul_Gamma_add_half (b/2)
    rw [show 2*(b/2)=b by ring,show b/2+1/2=(b+1)/2 by ring] at hh
    have ht : (2:ℝ)^(b-1)*(2:ℝ)^(1-b)=1 := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ)<2),show b-1+(1-b)=(0:ℝ) by ring,Real.rpow_zero]
    calc
      _ = ((2:ℝ)^(b-1)*(2:ℝ)^(1-b))*(Real.Gamma b*Real.sqrt Real.pi) := by rw [ht,one_mul]
      _ = _ := by linear_combination -(2:ℝ)^(b-1)*hh
  have hscale : Real.Gamma b*Real.Gamma d/Real.Gamma (b+d)*
      (Real.sqrt Real.pi*Real.Gamma (b+d)/(Real.Gamma (b/2+d)*Real.Gamma ((b+1)/2)))=
        (2:ℝ)^(b-1)*Real.Gamma (b/2)*Real.Gamma d/Real.Gamma (b/2+d) := by
    field_simp
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hdup
  have hc : Complex.Gamma (b:ℂ)*Complex.Gamma (d:ℂ)/Complex.Gamma ((b:ℂ)+(d:ℂ))≠0 :=
    div_ne_zero (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos hb) (Complex.Gamma_ne_zero_of_re_pos hd))
      (Complex.Gamma_ne_zero_of_re_pos (by simpa only [add_re,ofReal_re] using add_pos hb hd))
  apply mul_left_cancel₀ hc
  rw [Complex.ofReal_add,← he]
  have hcscale := congrArg Complex.ofReal hscale
  push_cast at hcscale ⊢
  simpa only [← Complex.Gamma_ofReal,Complex.ofReal_add] using hcscale.symm

/-- The actual balanced midpoint Gauss value is entire in its complex frequency.
Use: applies the identity theorem in second_summation without assuming a parameter continuation formula.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: reparametrize the already proved original entire wave core by omega=pi*lambda and gamma=g. -/
theorem midpoint_core_analytic (g : ℝ) (lam : ℂ) :
    AnalyticAt ℂ (fun l : ℂ => ordinaryHypergeometric ((g:ℂ)-l) ((g:ℂ)+l)
      ((g:ℂ)+1/2) (1/2:ℂ)) lam := by
  have hg : gamma (2*g-3/2)=g := by dsimp [gamma]; ring
  have hh := (waveCore_frequency_analytic (2*g-3/2) (x := (1/2:ℂ))
    (by norm_num) ((Real.pi:ℂ)*lam)).comp
      (f := fun l : ℂ => (Real.pi:ℂ)*l) (analyticAt_const.mul analyticAt_id)
  simpa only [Function.comp_def,waveCore,hg,mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)] using hh

/-- Gauss's second summation theorem holds for the actual reference hypergeometric function at every complex frequency, with no exceptional terminating or Gamma-zero cases.
Use: gives the exact formulas for both actual midpoint reference functions in MidpointFormula.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Source: Gauss's second summation theorem, DLMF 15.4.28, proved here.
Proof: the exact Euler integral evaluation proves equality when the
frequency is real, positive and sufficiently small. Both sides are
entire in frequency. This real interval accumulates at zero; the
community identity theorem gives equality on the whole complex plane. -/
theorem second_summation {g : ℝ} (hg : 0<g) (lam : ℂ) :
    ordinaryHypergeometric ((g:ℂ)-lam) ((g:ℂ)+lam) ((g:ℂ)+1/2) (1/2:ℂ)=
      (Real.sqrt Real.pi:ℂ)*Complex.Gamma ((g:ℂ)+1/2)*
        (Complex.Gamma (((g:ℂ)+1-lam)/2))⁻¹*
          (Complex.Gamma (((g:ℂ)+1+lam)/2))⁻¹ := by
  -- The actual entire functions agree on a concrete real interval, whose nonzero points accumulate at zero.
  let F : ℂ → ℂ := fun l => ordinaryHypergeometric ((g:ℂ)-l) ((g:ℂ)+l) ((g:ℂ)+1/2) (1/2:ℂ)
  let G : ℂ → ℂ := fun l => (Real.sqrt Real.pi:ℂ)*Complex.Gamma ((g:ℂ)+1/2)*
    (Complex.Gamma (((g:ℂ)+1-l)/2))⁻¹*(Complex.Gamma (((g:ℂ)+1+l)/2))⁻¹
  have hF : AnalyticOnNhd ℂ F univ := fun l _ => midpoint_core_analytic g l
  have hG : AnalyticOnNhd ℂ G univ := by
    intro l _
    apply AnalyticAt.mul
    · exact analyticAt_const.mul (Complex.differentiable_one_div_Gamma.analyticAt _ |>.comp
        ((analyticAt_const.sub analyticAt_id).div_const))
    · exact Complex.differentiable_one_div_Gamma.analyticAt _ |>.comp
        ((analyticAt_const.add analyticAt_id).div_const)
  have hreal {x : ℝ} (hx : x∈Ioo (0:ℝ) (min (g/2) (1/4))) : F (x:ℂ)=G (x:ℂ) := by
    have hb : 0<g+x := by linarith [hx.1]
    have hd : 0<(1/2:ℝ)-x := by linarith [(lt_min_iff.mp hx.2).2]
    have he := second_summation_real hb hd
    have h1 : g+x+2*((1/2:ℝ)-x)-1=g-x := by ring
    have h2 : g+x+((1/2:ℝ)-x)=g+1/2 := by ring
    have h3 : (g+x)/2+((1/2:ℝ)-x)=(g+1-x)/2 := by ring
    rw [h1,h2,h3,show (g+x+1)/2=(g+1+x)/2 by ring] at he
    dsimp [F,G]
    push_cast at he
    simp only [← Complex.Gamma_ofReal] at he
    push_cast at he
    simpa only [Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_div,
      Complex.ofReal_one,Complex.ofReal_ofNat,div_eq_mul_inv,mul_inv_rev,
      mul_assoc,mul_comm,mul_left_comm] using he
  have hε : 0<min (g/2) (1/4:ℝ) := lt_min (by linarith) (by norm_num)
  have hcl : (0:ℂ)∈closure ({l | F l=G l}\{0}) := by
    have hr : (0:ℝ)∈closure (Ioo (0:ℝ) (min (g/2) (1/4))) := by
      rw [closure_Ioo hε.ne]; exact ⟨le_rfl,hε.le⟩
    have hi := _root_.mem_closure_image Complex.continuous_ofReal.continuousAt hr
    rw [Complex.ofReal_zero] at hi
    apply (closure_mono (show Complex.ofReal '' Ioo (0:ℝ) (min (g/2) (1/4))⊆{l | F l=G l}\{0} from ?_)) hi
    rintro l ⟨x,hx,rfl⟩
    exact ⟨hreal hx,by simpa only [mem_singleton_iff,Complex.ofReal_eq_zero] using hx.1.ne'⟩
  exact hF.eqOn_of_preconnected_of_mem_closure hG isPreconnected_univ (mem_univ (0:ℂ)) hcl (mem_univ lam)

end
end jacobi.Reference.Hypergeometric
