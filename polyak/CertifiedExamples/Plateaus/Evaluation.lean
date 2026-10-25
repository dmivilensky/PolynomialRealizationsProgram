import polyak.CertifiedExamples.Plateaus.Blocks

namespace polyak.CertifiedExamples.Plateaus
open chebyshev2.Numerics

theorem value_plus {d : ℕ} (a b : E d) (v : Fin d → ℝ) :
    (plus a b).value v=a.value v+b.value v := rfl
theorem value_minus {d : ℕ} (a b : E d) (v : Fin d → ℝ) :
    (minus a b).value v=a.value v-b.value v := rfl
theorem value_times {d : ℕ} (a b : E d) (v : Fin d → ℝ) :
    (times a b).value v=a.value v*b.value v := rfl
theorem value_neg {d : ℕ} (a : E d) (v : Fin d → ℝ) :
    (IntervalExpr.neg a).value v= -a.value v := rfl
theorem value_variable {d : ℕ} (i : Fin d) (v : Fin d → ℝ) :
    (IntervalExpr.variable i).value v=v i := rfl

end polyak.CertifiedExamples.Plateaus
