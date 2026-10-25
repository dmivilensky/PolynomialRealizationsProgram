import polyak.General.IQC.Convolution

/-! Exact finite-sum recurrence of the causal convolution. -/
noncomputable section
namespace polyak.General.IQC
open Finset
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convolution_reverse (h : ℕ → ℝ) (x : ℕ → E) (n : ℕ) :
    convolution h x n=∑ j∈range (n+1),h (n-j) • x j := by
  change (∑ j∈range (n+1),h j • delay j x n)=_
  have he : (∑ j∈range (n+1),h j • delay j x n)=
      ∑ j∈range (n+1),h j • x (n-j):=by
    apply sum_congr rfl
    intro j hj
    simp [delay,show j≤n by have hh:=mem_range.mp hj; omega]
  rw [he,←sum_range_reflect]
  apply sum_congr rfl
  intro j hj
  simp only [Nat.add_sub_cancel]
  rw [show n-(n-j)=j by have hh:=mem_range.mp hj; omega]

@[simp] theorem convolution_zero (h : ℕ → ℝ) (x : ℕ → E) :
    convolution h x 0=h 0 • x 0 := by simp [convolution,delay]

theorem convolution_one (h : ℕ → ℝ) (x : ℕ → E) :
    convolution h x 1=h 1 • x 0+h 0 • x 1 := by
  simp [convolution,delay,sum_range_succ,add_comm]

theorem convolution_recurrence {h : ℕ → ℝ} {a b : ℝ}
    (hh : ∀ k,h (k+2)=a*h (k+1)-b*h k) (x : ℕ → E) (n : ℕ) :
    convolution h x (n+2)=a • convolution h x (n+1)-b • convolution h x n+
      h 0 • x (n+2)+(h 1-a*h 0) • x (n+1) := by
  rw [convolution_reverse,convolution_reverse,convolution_reverse]
  have h2 : (∑ j∈range (n+2+1),h (n+2-j) • x j)=
      (∑ j∈range (n+1),h (n+2-j) • x j)+h 1 • x (n+1)+h 0 • x (n+2):=by
    rw [show n+2+1=(n+1)+1+1 by omega,sum_range_succ,sum_range_succ]
    simp
  have h1 : (∑ j∈range (n+1+1),h (n+1-j) • x j)=
      (∑ j∈range (n+1),h (n+1-j) • x j)+h 0 • x (n+1):=by
    rw [sum_range_succ]
    simp
  rw [h2,h1,smul_add,smul_smul]
  have hs : (∑ j∈range (n+1),h (n+2-j) • x j)=
      a • (∑ j∈range (n+1),h (n+1-j) • x j)-
      b • (∑ j∈range (n+1),h (n-j) • x j):=by
    rw [Finset.smul_sum,Finset.smul_sum,←sum_sub_distrib]
    apply sum_congr rfl
    intro j hj
    have hjn : j≤n:=by have hhj:=mem_range.mp hj; omega
    rw [show n+2-j=(n-j)+2 by omega,hh]
    rw [show n-j+1=n+1-j by omega]
    module
  rw [hs]
  module

end polyak.General.IQC
