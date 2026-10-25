import polyak.ModeLocking.TwoLag.SecondJet

/-! Second jets of a factored double contact, independent of numerical data. -/
noncomputable section
namespace polyak.CertifiedExamples.Exact313
open ModeLocking.TwoLag

theorem square_slope (a : ℝ) : deriv (fun x : ℝ=>(x-a)^2) a=0 := by
  convert ((((hasDerivAt_id a).sub_const a).pow 2).deriv) using 1 <;> simp

theorem square_second (a : ℝ) : deriv^[2] (fun x : ℝ=>(x-a)^2) a=2 := by
  have hd : deriv (fun x : ℝ=>(x-a)^2)=(fun x=>2*(x-a)) := by
    funext x
    convert ((((hasDerivAt_id x).sub_const a).pow 2).deriv) using 1 <;> simp
  change deriv (deriv (fun x : ℝ=>(x-a)^2)) a=2
  rw [hd]
  convert ((((hasDerivAt_id a).sub_const a).const_mul 2).deriv) using 1 <;> simp

theorem second_square_factor {f : ℝ→ℝ} {a : ℝ} (hf : ContDiffAt ℝ 2 f a) :
    deriv^[2] (fun x=>(x-a)^2*f x) a=2*f a := by
  have he : (fun x=>(x-a)^2*f x)=(fun x=>f x*(x-a)^2) := by
    funext x
    ring
  rw [he,second_mul_at_double_zero hf (by fun_prop) (by simp) (square_slope a),square_second]
  ring

end polyak.CertifiedExamples.Exact313
