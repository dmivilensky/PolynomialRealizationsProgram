import polyak.General.Cubic
namespace polyak.General.Tuning
theorem H_cartesian (q:Tuning) (r c s:ℝ) (ht:c^2+s^2=1) :
    ((1-((r*c:ℝ):ℂ)-(r*s:ℝ)*Complex.I)*q.a (((r*c:ℝ):ℂ)+(r*s:ℝ)*Complex.I)*star (q.b (((r*c:ℝ):ℂ)+(r*s:ℝ)*Complex.I))).re=q.H r c := by
  simp only [a,b,H,pow_two,Complex.mul_re,Complex.mul_im,Complex.sub_re,Complex.sub_im,
    Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,Complex.one_re,Complex.one_im,mul_zero,zero_mul,
    add_zero,zero_add,sub_zero,Complex.star_def,Complex.conj_re,Complex.conj_im]
  have hs2 : s^2=1-c^2 := by linarith
  have hs4 : s^4=(1-c^2)^2 := by rw [show s^4=(s^2)^2 by ring,hs2]
  ring_nf
  rw [hs4,hs2]
  ring

 theorem H_complex (q:Tuning) (r ω:ℝ) :
     q.H r (Real.cos ω)=
       ((1-(r:ℂ)*Complex.exp ((ω:ℂ)*Complex.I))*
         q.a ((r:ℂ)*Complex.exp ((ω:ℂ)*Complex.I))*
         star (q.b ((r:ℂ)*Complex.exp ((ω:ℂ)*Complex.I)))).re := by
   have he : (r:ℂ)*Complex.exp ((ω:ℂ)*Complex.I)=
       ((r*Real.cos ω:ℝ):ℂ)+(r*Real.sin ω:ℝ)*Complex.I := by
     rw [Complex.exp_ofReal_mul_I]
     push_cast
     ring
   rw [he]
   simpa only [sub_add_eq_sub_sub] using
     (q.H_cartesian r (Real.cos ω) (Real.sin ω) (Real.cos_sq_add_sin_sq ω)).symm
end polyak.General.Tuning
