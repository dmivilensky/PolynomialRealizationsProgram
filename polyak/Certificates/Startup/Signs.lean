import polyak.Certificates.Startup.Codes
import polyak.Certificates.Startup.Check00
import polyak.Certificates.Startup.Check01
import polyak.Certificates.Startup.Check02
import polyak.Certificates.Startup.Check03
import polyak.Certificates.Startup.Check04
import polyak.Certificates.Startup.Check05
import polyak.Certificates.Startup.Check06
import polyak.Certificates.Startup.Check07
import polyak.Certificates.Startup.Check08
import polyak.Certificates.Startup.Check09
import polyak.Certificates.Startup.Check10
import polyak.Certificates.Startup.Check11
import polyak.Certificates.Startup.Check12
import polyak.Certificates.Startup.Check13
import polyak.Certificates.Startup.Check14
import polyak.Certificates.Startup.Check15
import polyak.Certificates.Startup.Check16
import polyak.Certificates.Startup.Check17
import polyak.Certificates.Startup.Check18
import polyak.Certificates.Startup.Check19
import polyak.Certificates.Startup.Check20
import polyak.Certificates.Startup.Check21
import polyak.Certificates.Startup.Check22
import polyak.Certificates.Startup.Check23
import polyak.Certificates.Startup.Check24
import polyak.Certificates.Startup.Check25
import polyak.Certificates.Startup.Check26
import polyak.Certificates.Startup.Check27
import polyak.Certificates.Startup.Check28
import polyak.Certificates.Startup.Check29
import polyak.Certificates.Startup.Check30
import polyak.Certificates.Startup.Check31
import polyak.Certificates.Startup.Check32
import polyak.Certificates.Startup.Check33
import polyak.Certificates.Startup.Check34
import polyak.Certificates.Startup.Check35
import polyak.Certificates.Startup.Check36
import polyak.Certificates.Startup.Check37
import polyak.Certificates.Startup.Check38
import polyak.Certificates.Startup.Check39
import polyak.Certificates.Startup.Check40
import polyak.Certificates.Startup.Check41
import polyak.Certificates.Startup.Check42
import polyak.Certificates.Startup.Check43

/-! Article: the 44 exact signs for the actual initialized-spiral source. -/
namespace polyak.Certificates.Startup.Signs
noncomputable section
open polyak.Realization.ExplicitSpiral
open polyak.Numerics.BivariateBranch
open polyak.Certificates.Startup
/-- Article: kernel-certified source sign 00, with its physical branch. -/
theorem sign00 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check00.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<((Source.constant r q (-1))+(Source.reserve q)) := by
  rw [Codes.check00Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check00.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check00Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 01, with its physical branch. -/
theorem sign01 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check01.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<((((Source.constant r q (-1))+(Source.reserve q)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm r q (-1)))) := by
  rw [Codes.check01Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check01.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check01Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 02, with its physical branch. -/
theorem sign02 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check02.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(Source.betaNorm r q (-1)))) := by
  rw [Codes.check02Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check02.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check02Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 03, with its physical branch. -/
theorem sign03 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check03.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<((Source.quadratic r (-1))+((((-1) : ℚ) : ℝ)*(phaseBudget r))) := by
  rw [Codes.check03Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check03.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check03Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 04, with its physical branch. -/
theorem sign04 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check04.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<((Source.constant r q (-1))+(Source.quadratic r (-1))+(Source.reserve q)+(Source.residue r q (-1) 0)) := by
  rw [Codes.check04Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check04.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check04Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 05, with its physical branch. -/
theorem sign05 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check05.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<((Source.residue r q (-1) 0)+((((-1) : ℚ) : ℝ)*(phaseBudget r))+(((2 : ℚ) : ℝ)*(Source.quadratic r (-1)))) := by
  rw [Codes.check05Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check05.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check05Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 06, with its physical branch. -/
theorem sign06 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check06.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<((Source.constant r q (-1))+(Source.quadratic r (-1))+(Source.reserve q)+(Source.residue r q (-1) 1)) := by
  rw [Codes.check06Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check06.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check06Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 07, with its physical branch. -/
theorem sign07 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check07.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<((Source.residue r q (-1) 1)+((((-1) : ℚ) : ℝ)*(phaseBudget r))+(((2 : ℚ) : ℝ)*(Source.quadratic r (-1)))) := by
  rw [Codes.check07Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check07.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check07Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 08, with its physical branch. -/
theorem sign08 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check08.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<((Source.constant r q (-1))+(Source.quadratic r (-1))+(Source.reserve q)+(Source.residue r q (-1) 2)) := by
  rw [Codes.check08Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check08.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check08Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 09, with its physical branch. -/
theorem sign09 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check09.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(((((-1) : ℚ) : ℝ)*(((phaseBudget r)+(Source.residue r q (-1) 2)))^2)+(((Source.constant r q (-1))+(Source.reserve q))*(((((-4) : ℚ) : ℝ)*(phaseBudget r))+(((4 : ℚ) : ℝ)*(Source.quadratic r (-1)))))) := by
  rw [Codes.check09Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check09.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check09Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 10, with its physical branch. -/
theorem sign10 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check10.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(((((-1) : ℚ) : ℝ)*(Source.betaNorm r q (-1)))+(((4 : ℚ) : ℝ)*((Source.quadratic r (-1)))^2*(r)^20)) := by
  rw [Codes.check10Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check10.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check10Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 11, with its physical branch. -/
theorem sign11 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check11.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<((Source.constant r q (-1))+(Source.reserve q)+((Source.quadratic r (-1))*(r)^20)) := by
  rw [Codes.check11Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check11.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check11Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 12, with its physical branch. -/
theorem sign12 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check12.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<((((Source.constant r q (-1))+(Source.reserve q)+((Source.quadratic r (-1))*(r)^20)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm r q (-1))*(r)^20)) := by
  rw [Codes.check12Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check12.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check12Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 13, with its physical branch. -/
theorem sign13 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check13.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<((Source.constant r q (1))+(Source.reserve q)) := by
  rw [Codes.check13Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check13.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check13Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 14, with its physical branch. -/
theorem sign14 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check14.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<((((Source.constant r q (1))+(Source.reserve q)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm r q (1)))) := by
  rw [Codes.check14Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check14.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check14Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 15, with its physical branch. -/
theorem sign15 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check15.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(((1 : ℚ) : ℝ)+((((-1) : ℚ) : ℝ)*(Source.betaNorm r q (1)))) := by
  rw [Codes.check15Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check15.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check15Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 16, with its physical branch. -/
theorem sign16 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check16.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<((Source.quadratic r (1))+((((-1) : ℚ) : ℝ)*(phaseBudget r))) := by
  rw [Codes.check16Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check16.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check16Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 17, with its physical branch. -/
theorem sign17 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check17.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<((Source.constant r q (1))+(Source.quadratic r (1))+(Source.reserve q)+(Source.residue r q (1) 0)) := by
  rw [Codes.check17Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check17.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check17Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 18, with its physical branch. -/
theorem sign18 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check18.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(((((-1) : ℚ) : ℝ)*(((phaseBudget r)+(Source.residue r q (1) 0)))^2)+(((Source.constant r q (1))+(Source.reserve q))*(((((-4) : ℚ) : ℝ)*(phaseBudget r))+(((4 : ℚ) : ℝ)*(Source.quadratic r (1)))))) := by
  rw [Codes.check18Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check18.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check18Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 19, with its physical branch. -/
theorem sign19 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check19.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<((Source.constant r q (1))+(Source.quadratic r (1))+(Source.reserve q)+(Source.residue r q (1) 1)) := by
  rw [Codes.check19Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check19.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check19Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 20, with its physical branch. -/
theorem sign20 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check20.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(((((-1) : ℚ) : ℝ)*(((phaseBudget r)+(Source.residue r q (1) 1)))^2)+(((Source.constant r q (1))+(Source.reserve q))*(((((-4) : ℚ) : ℝ)*(phaseBudget r))+(((4 : ℚ) : ℝ)*(Source.quadratic r (1)))))) := by
  rw [Codes.check20Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check20.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check20Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 21, with its physical branch. -/
theorem sign21 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check21.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<((Source.constant r q (1))+(Source.quadratic r (1))+(Source.reserve q)+(Source.residue r q (1) 2)) := by
  rw [Codes.check21Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check21.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check21Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 22, with its physical branch. -/
theorem sign22 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check22.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<((Source.residue r q (1) 2)+((((-1) : ℚ) : ℝ)*(phaseBudget r))+(((2 : ℚ) : ℝ)*(Source.quadratic r (1)))) := by
  rw [Codes.check22Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check22.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check22Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 23, with its physical branch. -/
theorem sign23 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check23.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(((((-1) : ℚ) : ℝ)*(Source.betaNorm r q (1)))+(((4 : ℚ) : ℝ)*((Source.quadratic r (1)))^2*(r)^20)) := by
  rw [Codes.check23Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check23.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check23Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 24, with its physical branch. -/
theorem sign24 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check24.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<((Source.constant r q (1))+(Source.reserve q)+((Source.quadratic r (1))*(r)^20)) := by
  rw [Codes.check24Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check24.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check24Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 25, with its physical branch. -/
theorem sign25 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check25.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<((((Source.constant r q (1))+(Source.reserve q)+((Source.quadratic r (1))*(r)^20)))^2+((((-1) : ℚ) : ℝ)*(Source.betaNorm r q (1))*(r)^20)) := by
  rw [Codes.check25Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check25.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check25Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 26, with its physical branch. -/
theorem sign26 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check26.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(Source.pairSlack r q (-1) 1) := by
  rw [Codes.check26Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check26.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check26Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 27, with its physical branch. -/
theorem sign27 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check27.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(Source.pairSlack r q (1) 1) := by
  rw [Codes.check27Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check27.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check27Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 28, with its physical branch. -/
theorem sign28 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check28.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(Source.pairSlack r q (-1) 2) := by
  rw [Codes.check28Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check28.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check28Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 29, with its physical branch. -/
theorem sign29 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check29.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(Source.pairSlack r q (1) 2) := by
  rw [Codes.check29Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check29.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check29Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 30, with its physical branch. -/
theorem sign30 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check30.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(Source.pairSlack r q (-1) 3) := by
  rw [Codes.check30Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check30.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check30Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 31, with its physical branch. -/
theorem sign31 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check31.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(Source.pairSlack r q (1) 3) := by
  rw [Codes.check31Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check31.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check31Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 32, with its physical branch. -/
theorem sign32 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check32.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(Source.pairSlack r q (-1) 4) := by
  rw [Codes.check32Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check32.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check32Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 33, with its physical branch. -/
theorem sign33 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check33.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(Source.pairSlack r q (1) 4) := by
  rw [Codes.check33Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check33.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check33Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 34, with its physical branch. -/
theorem sign34 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check34.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(Source.pairSlack r q (-1) 5) := by
  rw [Codes.check34Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check34.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check34Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 35, with its physical branch. -/
theorem sign35 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check35.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(Source.pairSlack r q (1) 5) := by
  rw [Codes.check35Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check35.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check35Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 36, with its physical branch. -/
theorem sign36 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check36.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(Source.pairSlack r q (-1) 6) := by
  rw [Codes.check36Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check36.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check36Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 37, with its physical branch. -/
theorem sign37 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check37.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(Source.pairSlack r q (1) 6) := by
  rw [Codes.check37Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check37.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check37Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 38, with its physical branch. -/
theorem sign38 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check38.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(Source.pairSlack r q (-1) 7) := by
  rw [Codes.check38Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check38.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check38Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 39, with its physical branch. -/
theorem sign39 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check39.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(Source.pairSlack r q (1) 7) := by
  rw [Codes.check39Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check39.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check39Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 40, with its physical branch. -/
theorem sign40 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check40.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(Source.pairSlack r q (-1) 8) := by
  rw [Codes.check40Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check40.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check40Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 41, with its physical branch. -/
theorem sign41 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check41.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(Source.pairSlack r q (1) 8) := by
  rw [Codes.check41Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check41.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check41Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 42, with its physical branch. -/
theorem sign42 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check42.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(Source.pairSlack r q (-1) 9) := by
  rw [Codes.check42Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check42.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check42Denominator (by kernel_decide) hr hq

/-- Article: kernel-certified source sign 43, with its physical branch. -/
theorem sign43 {r q : ℝ} (hr : 0<r) (hq : 0<q)
    (hI : r∈Check43.interval) (hF : polyak.Spiral.spiralPolynomial r q=0) :
    0<(Source.pairSlack r q (1) 9) := by
  rw [Codes.check43Code.exact (r,q) ⟨hr,hq⟩]
  apply div_pos
  · exact Check43.numerator_pos hI hr hq hF
  · exact polyak.Numerics.IntegerBivariate.positiveCoefficients_sound
      Codes.check43Denominator (by kernel_decide) hr hq

end
end polyak.Certificates.Startup.Signs
