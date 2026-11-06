import nesterov.Phase.Algebra

/-!
Article: Lemma E.1. Exact circle algebra for two real monic quadratics;
no stability, limiting argument, or positivity assumption is used.
-/
namespace nesterov.TwoStep
noncomputable section

def quad (S Q : ℝ) (z : ℂ) : ℂ := z^2-(S:ℂ)*z+Q
def circle (r ω : ℝ) : ℂ := (r:ℂ)*polyak.Waves.z 0 ω

def E0 (r Sμ SL Qμ QL : ℝ) : ℝ := r^4+Sμ*SL*r^2+Qμ*QL
def E1 (r Sμ SL QL : ℝ) : ℝ := SL*r^2+Sμ*QL
def E2 (r Sμ SL Qμ : ℝ) : ℝ := Sμ*r^2+Qμ*SL

theorem circle_normSq (r ω : ℝ) : Complex.normSq (circle r ω)=r^2 := by
  rw [circle,Complex.normSq_mul,Complex.normSq_ofReal]
  have hn : Complex.normSq (polyak.Waves.z 0 ω)=1 := by
    simpa only [pow_one,mul_zero,Real.exp_zero] using polyak.Waves.normSq_z_pow 0 ω 1
  rw [hn,mul_one,pow_two]

theorem circle_pow_re (r ω : ℝ) (n : ℕ) : (circle r ω^n).re=r^n*Real.cos (n*ω) := by
  rw [circle,mul_pow,←Complex.ofReal_pow,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hh := polyak.Waves.z_pow_re 0 ω n
  simpa only [mul_zero,Real.exp_zero,one_mul] using congrArg (fun a : ℝ=>r^n*a) hh

theorem quad_product {z : ℂ} {r : ℝ} (hz : Complex.normSq z=r^2) (Sμ SL Qμ QL : ℝ) :
    quad Sμ Qμ z*star (quad SL QL z)=
      (E0 r Sμ SL Qμ QL:ℂ)-(E1 r Sμ SL QL:ℂ)*z-(E2 r Sμ SL Qμ:ℂ)*star z+
        (QL:ℂ)*z^2+(Qμ:ℂ)*(star z)^2 := by
  have hzz : z*star z=(r:ℂ)^2 := by
    rw [Complex.star_def,Complex.mul_conj,hz]
    norm_cast
  have hr (x : ℝ) : star (x:ℂ)=(x:ℂ) := by simp
  unfold quad E0 E1 E2
  simp only [star_add,star_sub,star_pow,star_mul,hr]
  push_cast
  linear_combination (z*star z+(r:ℂ)^2-(SL:ℂ)*z-(Sμ:ℂ)*star z+(Sμ:ℂ)*SL)*hzz

theorem lagOne_complex {z : ℂ} {r : ℝ} (hz : Complex.normSq z=r^2) (Sμ SL Qμ QL : ℝ) :
    (1-z)*quad Sμ Qμ z*star (quad SL QL z)=
      (E0 r Sμ SL Qμ QL:ℂ)+(r:ℂ)^2*E2 r Sμ SL Qμ-
        ((E0 r Sμ SL Qμ QL:ℂ)+E1 r Sμ SL QL)*z-
        ((E2 r Sμ SL Qμ:ℂ)+(Qμ:ℂ)*r^2)*star z+
        ((E1 r Sμ SL QL:ℂ)+QL)*z^2+(Qμ:ℂ)*(star z)^2-(QL:ℂ)*z^3 := by
  rw [mul_assoc,quad_product hz]
  have hzz : z*star z=(r:ℂ)^2 := by
    rw [Complex.star_def,Complex.mul_conj,hz]
    norm_cast
  linear_combination ((E2 r Sμ SL Qμ:ℂ)-(Qμ:ℂ)*star z)*hzz


theorem lagOne_trigonometric (r ω Sμ SL Qμ QL : ℝ) :
    ((1-circle r ω)*quad Sμ Qμ (circle r ω)*star (quad SL QL (circle r ω))).re=
      E0 r Sμ SL Qμ QL+r^2*E2 r Sμ SL Qμ-
        r*(E0 r Sμ SL Qμ QL+E1 r Sμ SL QL+E2 r Sμ SL Qμ+Qμ*r^2)*Real.cos ω+
        r^2*(E1 r Sμ SL QL+Qμ+QL)*Real.cos (2*ω)-QL*r^3*Real.cos (3*ω) := by
  rw [lagOne_complex (circle_normSq r ω)]
  have hs (n : ℕ) : ((star (circle r ω))^n).re=(circle r ω^n).re := by
    rw [←star_pow,Complex.star_def,Complex.conj_re]
  have hz : (circle r ω).re=r*Real.cos ω := by simpa using circle_pow_re r ω 1
  have hzstar : (star (circle r ω)).re=r*Real.cos ω := by
    rw [Complex.star_def,Complex.conj_re,hz]
  simp only [←Complex.ofReal_pow,Complex.add_re,Complex.add_im,Complex.sub_re,
    Complex.mul_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,add_zero,
    zero_mul,mul_zero,sub_zero,hs,circle_pow_re,hz,hzstar]
  norm_num
  ring

end
end nesterov.TwoStep
