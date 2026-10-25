import polyak.Farey.Certificates.Fan

/-! The literal two-lag specialization of the full fan formula. -/
noncomputable section
namespace polyak.Farey.Certificates
open Levels Set
open Spectral (chebT chebU)

def twoLagLeft (q:General.Tuning) (K:ℕ) (r γ c:ℝ) : ℝ:=
  q.Xi c*((1-c)+r*(1-chebT K c)+γ)
def twoLagRight (K:ℕ) (r c:ℝ) : ℝ:=
  (1-c^2)*(1-r*chebU (K-1) c)
def twoLagGap (q:General.Tuning) (K:ℕ) (r γ c:ℝ) : ℝ:=
  twoLagRight K r c-twoLagLeft q K r γ c

theorem twoLag_fan_left (q:General.Tuning) (K:ℕ) (r γ c:ℝ) :
    fanLeft q K {0} {1} (fun _=>1) (fun _=>r) γ c=twoLagLeft q K r γ c := by
  simp [fanLeft,twoLagLeft,chebT]
theorem twoLag_fan_right (K:ℕ) (r c:ℝ) :
    fanRight K {0} {1} (fun _=>1) (fun _=>r) c=twoLagRight K r c := by
  simp [fanRight,twoLagRight,chebU]

theorem two_lag_rate_lt_one (q:General.Tuning) {K:ℕ} (hK:2≤K) {r γ:ℝ}
    (hr:0≤r) (hγ:0<γ)
    (hP:∀c∈Icc (-1:ℝ) 1,twoLagLeft q K r γ c<twoLagRight K r c) : q.rate<1 := by
  apply fan_formula_rate_lt_one q hK {0} {1} (by simp) (fun _=>1) (fun _=>r)
    (by intro m hm; norm_num) (by intro m hm; exact hr) hγ
  intro c hc
  simpa only [twoLag_fan_left,twoLag_fan_right] using hP c hc

theorem positive_twoLagGap_rate_lt_one (q:General.Tuning) {K:ℕ} (hK:2≤K) {r γ:ℝ}
    (hr:0≤r) (hγ:0<γ) (hP:∀c∈Icc (-1:ℝ) 1,0<twoLagGap q K r γ c) : q.rate<1 :=
  two_lag_rate_lt_one q hK hr hγ (fun c hc=>sub_pos.mp (hP c hc))

end polyak.Farey.Certificates
