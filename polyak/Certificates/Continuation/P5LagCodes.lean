import polyak.Boundary.P5.LagCode
import polyak.Numerics.KernelDecide

/-! Article: (p5arc), exact Chebyshev and shifted divided coefficient proposals.
Every base array satisfies the independent Chebyshev recurrence, and every shift
and exact division is checked separately by the Lean kernel. -/
noncomputable section
namespace polyak.Certificates.Continuation.P5Lags
open LeanCert.Engine Polynomial Boundary.P5
open Boundary.P2 Numerics

def T00 : QPoly := QPoly.constant 1

theorem T00_exact (x : ℝ) : aeval x T00.toPoly=Spectral.chebT 0 x := by
  simp [T00,QPoly.toPoly_constant,Spectral.chebT]

def T01 : QPoly := QPoly.X

theorem T01_exact (x : ℝ) : aeval x T01.toPoly=Spectral.chebT 1 x := by
  simp [T01,QPoly.toPoly_X,Spectral.chebT]

def T02 : QPoly := ⟨#[-1,0,2]⟩

private theorem T02_checked : polynomialCheck T02
    (((QPoly.constant 2).mul QPoly.X).mul T01 |>.add ((QPoly.constant (-1)).mul T00))=true := by kernel_decide

theorem T02_exact (x : ℝ) : aeval x T02.toPoly=Spectral.chebT 2 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound T02_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,T01_exact,T00_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Spiral.chebT_recurrence x 0
  change Spectral.chebT 2 x=2*x*Spectral.chebT 1 x-Spectral.chebT 0 x at hr
  rw [hr]
  linear_combination he

def T03 : QPoly := ⟨#[0,-3,0,4]⟩

private theorem T03_checked : polynomialCheck T03
    (((QPoly.constant 2).mul QPoly.X).mul T02 |>.add ((QPoly.constant (-1)).mul T01))=true := by kernel_decide

theorem T03_exact (x : ℝ) : aeval x T03.toPoly=Spectral.chebT 3 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound T03_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,T02_exact,T01_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Spiral.chebT_recurrence x 1
  change Spectral.chebT 3 x=2*x*Spectral.chebT 2 x-Spectral.chebT 1 x at hr
  rw [hr]
  linear_combination he

def T04 : QPoly := ⟨#[1,0,-8,0,8]⟩

private theorem T04_checked : polynomialCheck T04
    (((QPoly.constant 2).mul QPoly.X).mul T03 |>.add ((QPoly.constant (-1)).mul T02))=true := by kernel_decide

theorem T04_exact (x : ℝ) : aeval x T04.toPoly=Spectral.chebT 4 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound T04_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,T03_exact,T02_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Spiral.chebT_recurrence x 2
  change Spectral.chebT 4 x=2*x*Spectral.chebT 3 x-Spectral.chebT 2 x at hr
  rw [hr]
  linear_combination he

def T05 : QPoly := ⟨#[0,5,0,-20,0,16]⟩

private theorem T05_checked : polynomialCheck T05
    (((QPoly.constant 2).mul QPoly.X).mul T04 |>.add ((QPoly.constant (-1)).mul T03))=true := by kernel_decide

theorem T05_exact (x : ℝ) : aeval x T05.toPoly=Spectral.chebT 5 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound T05_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,T04_exact,T03_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Spiral.chebT_recurrence x 3
  change Spectral.chebT 5 x=2*x*Spectral.chebT 4 x-Spectral.chebT 3 x at hr
  rw [hr]
  linear_combination he

def T06 : QPoly := ⟨#[-1,0,18,0,-48,0,32]⟩

private theorem T06_checked : polynomialCheck T06
    (((QPoly.constant 2).mul QPoly.X).mul T05 |>.add ((QPoly.constant (-1)).mul T04))=true := by kernel_decide

theorem T06_exact (x : ℝ) : aeval x T06.toPoly=Spectral.chebT 6 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound T06_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,T05_exact,T04_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Spiral.chebT_recurrence x 4
  change Spectral.chebT 6 x=2*x*Spectral.chebT 5 x-Spectral.chebT 4 x at hr
  rw [hr]
  linear_combination he

def T07 : QPoly := ⟨#[0,-7,0,56,0,-112,0,64]⟩

private theorem T07_checked : polynomialCheck T07
    (((QPoly.constant 2).mul QPoly.X).mul T06 |>.add ((QPoly.constant (-1)).mul T05))=true := by kernel_decide

theorem T07_exact (x : ℝ) : aeval x T07.toPoly=Spectral.chebT 7 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound T07_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,T06_exact,T05_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Spiral.chebT_recurrence x 5
  change Spectral.chebT 7 x=2*x*Spectral.chebT 6 x-Spectral.chebT 5 x at hr
  rw [hr]
  linear_combination he

def T08 : QPoly := ⟨#[1,0,-32,0,160,0,-256,0,128]⟩

private theorem T08_checked : polynomialCheck T08
    (((QPoly.constant 2).mul QPoly.X).mul T07 |>.add ((QPoly.constant (-1)).mul T06))=true := by kernel_decide

theorem T08_exact (x : ℝ) : aeval x T08.toPoly=Spectral.chebT 8 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound T08_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,T07_exact,T06_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Spiral.chebT_recurrence x 6
  change Spectral.chebT 8 x=2*x*Spectral.chebT 7 x-Spectral.chebT 6 x at hr
  rw [hr]
  linear_combination he

def T09 : QPoly := ⟨#[0,9,0,-120,0,432,0,-576,0,256]⟩

private theorem T09_checked : polynomialCheck T09
    (((QPoly.constant 2).mul QPoly.X).mul T08 |>.add ((QPoly.constant (-1)).mul T07))=true := by kernel_decide

theorem T09_exact (x : ℝ) : aeval x T09.toPoly=Spectral.chebT 9 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound T09_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,T08_exact,T07_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Spiral.chebT_recurrence x 7
  change Spectral.chebT 9 x=2*x*Spectral.chebT 8 x-Spectral.chebT 7 x at hr
  rw [hr]
  linear_combination he

def T10 : QPoly := ⟨#[-1,0,50,0,-400,0,1120,0,-1280,0,512]⟩

private theorem T10_checked : polynomialCheck T10
    (((QPoly.constant 2).mul QPoly.X).mul T09 |>.add ((QPoly.constant (-1)).mul T08))=true := by kernel_decide

theorem T10_exact (x : ℝ) : aeval x T10.toPoly=Spectral.chebT 10 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound T10_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,T09_exact,T08_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Spiral.chebT_recurrence x 8
  change Spectral.chebT 10 x=2*x*Spectral.chebT 9 x-Spectral.chebT 8 x at hr
  rw [hr]
  linear_combination he

def T11 : QPoly := ⟨#[0,-11,0,220,0,-1232,0,2816,0,-2816,0,1024]⟩

private theorem T11_checked : polynomialCheck T11
    (((QPoly.constant 2).mul QPoly.X).mul T10 |>.add ((QPoly.constant (-1)).mul T09))=true := by kernel_decide

theorem T11_exact (x : ℝ) : aeval x T11.toPoly=Spectral.chebT 11 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound T11_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,T10_exact,T09_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Spiral.chebT_recurrence x 9
  change Spectral.chebT 11 x=2*x*Spectral.chebT 10 x-Spectral.chebT 9 x at hr
  rw [hr]
  linear_combination he

def T12 : QPoly := ⟨#[1,0,-72,0,840,0,-3584,0,6912,0,-6144,0,2048]⟩

private theorem T12_checked : polynomialCheck T12
    (((QPoly.constant 2).mul QPoly.X).mul T11 |>.add ((QPoly.constant (-1)).mul T10))=true := by kernel_decide

theorem T12_exact (x : ℝ) : aeval x T12.toPoly=Spectral.chebT 12 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound T12_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,T11_exact,T10_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Spiral.chebT_recurrence x 10
  change Spectral.chebT 12 x=2*x*Spectral.chebT 11 x-Spectral.chebT 10 x at hr
  rw [hr]
  linear_combination he

def T13 : QPoly := ⟨#[0,13,0,-364,0,2912,0,-9984,0,16640,0,-13312,0,4096]⟩

private theorem T13_checked : polynomialCheck T13
    (((QPoly.constant 2).mul QPoly.X).mul T12 |>.add ((QPoly.constant (-1)).mul T11))=true := by kernel_decide

theorem T13_exact (x : ℝ) : aeval x T13.toPoly=Spectral.chebT 13 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound T13_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,T12_exact,T11_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Spiral.chebT_recurrence x 11
  change Spectral.chebT 13 x=2*x*Spectral.chebT 12 x-Spectral.chebT 11 x at hr
  rw [hr]
  linear_combination he

def T14 : QPoly := ⟨#[-1,0,98,0,-1568,0,9408,0,-26880,0,39424,0,-28672,0,8192]⟩

private theorem T14_checked : polynomialCheck T14
    (((QPoly.constant 2).mul QPoly.X).mul T13 |>.add ((QPoly.constant (-1)).mul T12))=true := by kernel_decide

theorem T14_exact (x : ℝ) : aeval x T14.toPoly=Spectral.chebT 14 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound T14_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,T13_exact,T12_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Spiral.chebT_recurrence x 12
  change Spectral.chebT 14 x=2*x*Spectral.chebT 13 x-Spectral.chebT 12 x at hr
  rw [hr]
  linear_combination he

def T15 : QPoly := ⟨#[0,-15,0,560,0,-6048,0,28800,0,-70400,0,92160,0,-61440,0,16384]⟩

private theorem T15_checked : polynomialCheck T15
    (((QPoly.constant 2).mul QPoly.X).mul T14 |>.add ((QPoly.constant (-1)).mul T13))=true := by kernel_decide

theorem T15_exact (x : ℝ) : aeval x T15.toPoly=Spectral.chebT 15 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound T15_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,T14_exact,T13_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Spiral.chebT_recurrence x 13
  change Spectral.chebT 15 x=2*x*Spectral.chebT 14 x-Spectral.chebT 13 x at hr
  rw [hr]
  linear_combination he

def T16 : QPoly := ⟨#[1,0,-128,0,2688,0,-21504,0,84480,0,-180224,0,212992,0,-131072,0,32768]⟩

private theorem T16_checked : polynomialCheck T16
    (((QPoly.constant 2).mul QPoly.X).mul T15 |>.add ((QPoly.constant (-1)).mul T14))=true := by kernel_decide

theorem T16_exact (x : ℝ) : aeval x T16.toPoly=Spectral.chebT 16 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound T16_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,T15_exact,T14_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Spiral.chebT_recurrence x 14
  change Spectral.chebT 16 x=2*x*Spectral.chebT 15 x-Spectral.chebT 14 x at hr
  rw [hr]
  linear_combination he

def T17 : QPoly := ⟨#[0,17,0,-816,0,11424,0,-71808,0,239360,0,-452608,0,487424,0,-278528,0,65536]⟩

private theorem T17_checked : polynomialCheck T17
    (((QPoly.constant 2).mul QPoly.X).mul T16 |>.add ((QPoly.constant (-1)).mul T15))=true := by kernel_decide

theorem T17_exact (x : ℝ) : aeval x T17.toPoly=Spectral.chebT 17 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound T17_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,T16_exact,T15_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Spiral.chebT_recurrence x 15
  change Spectral.chebT 17 x=2*x*Spectral.chebT 16 x-Spectral.chebT 15 x at hr
  rw [hr]
  linear_combination he

def T18 : QPoly := ⟨#[-1,0,162,0,-4320,0,44352,0,-228096,0,658944,0,-1118208,0,1105920,0,-589824,0,131072]⟩

private theorem T18_checked : polynomialCheck T18
    (((QPoly.constant 2).mul QPoly.X).mul T17 |>.add ((QPoly.constant (-1)).mul T16))=true := by kernel_decide

theorem T18_exact (x : ℝ) : aeval x T18.toPoly=Spectral.chebT 18 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound T18_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,T17_exact,T16_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Spiral.chebT_recurrence x 16
  change Spectral.chebT 18 x=2*x*Spectral.chebT 17 x-Spectral.chebT 16 x at hr
  rw [hr]
  linear_combination he

def T19 : QPoly := ⟨#[0,-19,0,1140,0,-20064,0,160512,0,-695552,0,1770496,0,-2723840,0,2490368,0,-1245184,0,262144]⟩

private theorem T19_checked : polynomialCheck T19
    (((QPoly.constant 2).mul QPoly.X).mul T18 |>.add ((QPoly.constant (-1)).mul T17))=true := by kernel_decide

theorem T19_exact (x : ℝ) : aeval x T19.toPoly=Spectral.chebT 19 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound T19_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,T18_exact,T17_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Spiral.chebT_recurrence x 17
  change Spectral.chebT 19 x=2*x*Spectral.chebT 18 x-Spectral.chebT 17 x at hr
  rw [hr]
  linear_combination he

def T20 : QPoly := ⟨#[1,0,-200,0,6600,0,-84480,0,549120,0,-2050048,0,4659200,0,-6553600,0,5570560,0,-2621440,0,524288]⟩

private theorem T20_checked : polynomialCheck T20
    (((QPoly.constant 2).mul QPoly.X).mul T19 |>.add ((QPoly.constant (-1)).mul T18))=true := by kernel_decide

theorem T20_exact (x : ℝ) : aeval x T20.toPoly=Spectral.chebT 20 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound T20_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,T19_exact,T18_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Spiral.chebT_recurrence x 18
  change Spectral.chebT 20 x=2*x*Spectral.chebT 19 x-Spectral.chebT 18 x at hr
  rw [hr]
  linear_combination he

def T21 : QPoly := ⟨#[0,21,0,-1540,0,33264,0,-329472,0,1793792,0,-5870592,0,12042240,0,-15597568,0,12386304,0,-5505024,0,1048576]⟩

private theorem T21_checked : polynomialCheck T21
    (((QPoly.constant 2).mul QPoly.X).mul T20 |>.add ((QPoly.constant (-1)).mul T19))=true := by kernel_decide

theorem T21_exact (x : ℝ) : aeval x T21.toPoly=Spectral.chebT 21 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound T21_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,T20_exact,T19_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Spiral.chebT_recurrence x 19
  change Spectral.chebT 21 x=2*x*Spectral.chebT 20 x-Spectral.chebT 19 x at hr
  rw [hr]
  linear_combination he

def T22 : QPoly := ⟨#[-1,0,242,0,-9680,0,151008,0,-1208064,0,5637632,0,-16400384,0,30638080,0,-36765696,0,27394048,0,-11534336,0,2097152]⟩

private theorem T22_checked : polynomialCheck T22
    (((QPoly.constant 2).mul QPoly.X).mul T21 |>.add ((QPoly.constant (-1)).mul T20))=true := by kernel_decide

theorem T22_exact (x : ℝ) : aeval x T22.toPoly=Spectral.chebT 22 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound T22_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,T21_exact,T20_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Spiral.chebT_recurrence x 20
  change Spectral.chebT 22 x=2*x*Spectral.chebT 21 x-Spectral.chebT 20 x at hr
  rw [hr]
  linear_combination he

def T23 : QPoly := ⟨#[0,-23,0,2024,0,-52624,0,631488,0,-4209920,0,17145856,0,-44843008,0,76873728,0,-85917696,0,60293120,0,-24117248,0,4194304]⟩

private theorem T23_checked : polynomialCheck T23
    (((QPoly.constant 2).mul QPoly.X).mul T22 |>.add ((QPoly.constant (-1)).mul T21))=true := by kernel_decide

theorem T23_exact (x : ℝ) : aeval x T23.toPoly=Spectral.chebT 23 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound T23_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,T22_exact,T21_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Spiral.chebT_recurrence x 21
  change Spectral.chebT 23 x=2*x*Spectral.chebT 22 x-Spectral.chebT 21 x at hr
  rw [hr]
  linear_combination he

def U00 : QPoly := QPoly.constant 1

theorem U00_exact (x : ℝ) : aeval x U00.toPoly=Spectral.chebU 0 x := by
  simp [U00,QPoly.toPoly_constant,Spectral.chebU]

def U01 : QPoly := (QPoly.constant 2).mul QPoly.X

theorem U01_exact (x : ℝ) : aeval x U01.toPoly=Spectral.chebU 1 x := by
  simp [U01,QPoly.toPoly_constant,QPoly.toPoly_X,QPoly.toPoly_mul,Spectral.chebU]

def U02 : QPoly := ⟨#[-1,0,4]⟩

private theorem U02_checked : polynomialCheck U02
    (((QPoly.constant 2).mul QPoly.X).mul U01 |>.add ((QPoly.constant (-1)).mul U00))=true := by kernel_decide

theorem U02_exact (x : ℝ) : aeval x U02.toPoly=Spectral.chebU 2 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound U02_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,U01_exact,U00_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Boundary.P5.chebU_recurrence x 0
  change Spectral.chebU 2 x=2*x*Spectral.chebU 1 x-Spectral.chebU 0 x at hr
  rw [hr]
  linear_combination he

def U03 : QPoly := ⟨#[0,-4,0,8]⟩

private theorem U03_checked : polynomialCheck U03
    (((QPoly.constant 2).mul QPoly.X).mul U02 |>.add ((QPoly.constant (-1)).mul U01))=true := by kernel_decide

theorem U03_exact (x : ℝ) : aeval x U03.toPoly=Spectral.chebU 3 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound U03_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,U02_exact,U01_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Boundary.P5.chebU_recurrence x 1
  change Spectral.chebU 3 x=2*x*Spectral.chebU 2 x-Spectral.chebU 1 x at hr
  rw [hr]
  linear_combination he

def U04 : QPoly := ⟨#[1,0,-12,0,16]⟩

private theorem U04_checked : polynomialCheck U04
    (((QPoly.constant 2).mul QPoly.X).mul U03 |>.add ((QPoly.constant (-1)).mul U02))=true := by kernel_decide

theorem U04_exact (x : ℝ) : aeval x U04.toPoly=Spectral.chebU 4 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound U04_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,U03_exact,U02_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Boundary.P5.chebU_recurrence x 2
  change Spectral.chebU 4 x=2*x*Spectral.chebU 3 x-Spectral.chebU 2 x at hr
  rw [hr]
  linear_combination he

def U05 : QPoly := ⟨#[0,6,0,-32,0,32]⟩

private theorem U05_checked : polynomialCheck U05
    (((QPoly.constant 2).mul QPoly.X).mul U04 |>.add ((QPoly.constant (-1)).mul U03))=true := by kernel_decide

theorem U05_exact (x : ℝ) : aeval x U05.toPoly=Spectral.chebU 5 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound U05_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,U04_exact,U03_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Boundary.P5.chebU_recurrence x 3
  change Spectral.chebU 5 x=2*x*Spectral.chebU 4 x-Spectral.chebU 3 x at hr
  rw [hr]
  linear_combination he

def U06 : QPoly := ⟨#[-1,0,24,0,-80,0,64]⟩

private theorem U06_checked : polynomialCheck U06
    (((QPoly.constant 2).mul QPoly.X).mul U05 |>.add ((QPoly.constant (-1)).mul U04))=true := by kernel_decide

theorem U06_exact (x : ℝ) : aeval x U06.toPoly=Spectral.chebU 6 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound U06_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,U05_exact,U04_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Boundary.P5.chebU_recurrence x 4
  change Spectral.chebU 6 x=2*x*Spectral.chebU 5 x-Spectral.chebU 4 x at hr
  rw [hr]
  linear_combination he

def U07 : QPoly := ⟨#[0,-8,0,80,0,-192,0,128]⟩

private theorem U07_checked : polynomialCheck U07
    (((QPoly.constant 2).mul QPoly.X).mul U06 |>.add ((QPoly.constant (-1)).mul U05))=true := by kernel_decide

theorem U07_exact (x : ℝ) : aeval x U07.toPoly=Spectral.chebU 7 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound U07_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,U06_exact,U05_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Boundary.P5.chebU_recurrence x 5
  change Spectral.chebU 7 x=2*x*Spectral.chebU 6 x-Spectral.chebU 5 x at hr
  rw [hr]
  linear_combination he

def U08 : QPoly := ⟨#[1,0,-40,0,240,0,-448,0,256]⟩

private theorem U08_checked : polynomialCheck U08
    (((QPoly.constant 2).mul QPoly.X).mul U07 |>.add ((QPoly.constant (-1)).mul U06))=true := by kernel_decide

theorem U08_exact (x : ℝ) : aeval x U08.toPoly=Spectral.chebU 8 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound U08_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,U07_exact,U06_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Boundary.P5.chebU_recurrence x 6
  change Spectral.chebU 8 x=2*x*Spectral.chebU 7 x-Spectral.chebU 6 x at hr
  rw [hr]
  linear_combination he

def U09 : QPoly := ⟨#[0,10,0,-160,0,672,0,-1024,0,512]⟩

private theorem U09_checked : polynomialCheck U09
    (((QPoly.constant 2).mul QPoly.X).mul U08 |>.add ((QPoly.constant (-1)).mul U07))=true := by kernel_decide

theorem U09_exact (x : ℝ) : aeval x U09.toPoly=Spectral.chebU 9 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound U09_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,U08_exact,U07_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Boundary.P5.chebU_recurrence x 7
  change Spectral.chebU 9 x=2*x*Spectral.chebU 8 x-Spectral.chebU 7 x at hr
  rw [hr]
  linear_combination he

def U10 : QPoly := ⟨#[-1,0,60,0,-560,0,1792,0,-2304,0,1024]⟩

private theorem U10_checked : polynomialCheck U10
    (((QPoly.constant 2).mul QPoly.X).mul U09 |>.add ((QPoly.constant (-1)).mul U08))=true := by kernel_decide

theorem U10_exact (x : ℝ) : aeval x U10.toPoly=Spectral.chebU 10 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound U10_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,U09_exact,U08_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Boundary.P5.chebU_recurrence x 8
  change Spectral.chebU 10 x=2*x*Spectral.chebU 9 x-Spectral.chebU 8 x at hr
  rw [hr]
  linear_combination he

def U11 : QPoly := ⟨#[0,-12,0,280,0,-1792,0,4608,0,-5120,0,2048]⟩

private theorem U11_checked : polynomialCheck U11
    (((QPoly.constant 2).mul QPoly.X).mul U10 |>.add ((QPoly.constant (-1)).mul U09))=true := by kernel_decide

theorem U11_exact (x : ℝ) : aeval x U11.toPoly=Spectral.chebU 11 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound U11_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,U10_exact,U09_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Boundary.P5.chebU_recurrence x 9
  change Spectral.chebU 11 x=2*x*Spectral.chebU 10 x-Spectral.chebU 9 x at hr
  rw [hr]
  linear_combination he

def U12 : QPoly := ⟨#[1,0,-84,0,1120,0,-5376,0,11520,0,-11264,0,4096]⟩

private theorem U12_checked : polynomialCheck U12
    (((QPoly.constant 2).mul QPoly.X).mul U11 |>.add ((QPoly.constant (-1)).mul U10))=true := by kernel_decide

theorem U12_exact (x : ℝ) : aeval x U12.toPoly=Spectral.chebU 12 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound U12_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,U11_exact,U10_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Boundary.P5.chebU_recurrence x 10
  change Spectral.chebU 12 x=2*x*Spectral.chebU 11 x-Spectral.chebU 10 x at hr
  rw [hr]
  linear_combination he

def U13 : QPoly := ⟨#[0,14,0,-448,0,4032,0,-15360,0,28160,0,-24576,0,8192]⟩

private theorem U13_checked : polynomialCheck U13
    (((QPoly.constant 2).mul QPoly.X).mul U12 |>.add ((QPoly.constant (-1)).mul U11))=true := by kernel_decide

theorem U13_exact (x : ℝ) : aeval x U13.toPoly=Spectral.chebU 13 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound U13_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,U12_exact,U11_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Boundary.P5.chebU_recurrence x 11
  change Spectral.chebU 13 x=2*x*Spectral.chebU 12 x-Spectral.chebU 11 x at hr
  rw [hr]
  linear_combination he

def U14 : QPoly := ⟨#[-1,0,112,0,-2016,0,13440,0,-42240,0,67584,0,-53248,0,16384]⟩

private theorem U14_checked : polynomialCheck U14
    (((QPoly.constant 2).mul QPoly.X).mul U13 |>.add ((QPoly.constant (-1)).mul U12))=true := by kernel_decide

theorem U14_exact (x : ℝ) : aeval x U14.toPoly=Spectral.chebU 14 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound U14_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,U13_exact,U12_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Boundary.P5.chebU_recurrence x 12
  change Spectral.chebU 14 x=2*x*Spectral.chebU 13 x-Spectral.chebU 12 x at hr
  rw [hr]
  linear_combination he

def U15 : QPoly := ⟨#[0,-16,0,672,0,-8064,0,42240,0,-112640,0,159744,0,-114688,0,32768]⟩

private theorem U15_checked : polynomialCheck U15
    (((QPoly.constant 2).mul QPoly.X).mul U14 |>.add ((QPoly.constant (-1)).mul U13))=true := by kernel_decide

theorem U15_exact (x : ℝ) : aeval x U15.toPoly=Spectral.chebU 15 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound U15_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,U14_exact,U13_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Boundary.P5.chebU_recurrence x 13
  change Spectral.chebU 15 x=2*x*Spectral.chebU 14 x-Spectral.chebU 13 x at hr
  rw [hr]
  linear_combination he

def U16 : QPoly := ⟨#[1,0,-144,0,3360,0,-29568,0,126720,0,-292864,0,372736,0,-245760,0,65536]⟩

private theorem U16_checked : polynomialCheck U16
    (((QPoly.constant 2).mul QPoly.X).mul U15 |>.add ((QPoly.constant (-1)).mul U14))=true := by kernel_decide

theorem U16_exact (x : ℝ) : aeval x U16.toPoly=Spectral.chebU 16 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound U16_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,U15_exact,U14_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Boundary.P5.chebU_recurrence x 14
  change Spectral.chebU 16 x=2*x*Spectral.chebU 15 x-Spectral.chebU 14 x at hr
  rw [hr]
  linear_combination he

def U17 : QPoly := ⟨#[0,18,0,-960,0,14784,0,-101376,0,366080,0,-745472,0,860160,0,-524288,0,131072]⟩

private theorem U17_checked : polynomialCheck U17
    (((QPoly.constant 2).mul QPoly.X).mul U16 |>.add ((QPoly.constant (-1)).mul U15))=true := by kernel_decide

theorem U17_exact (x : ℝ) : aeval x U17.toPoly=Spectral.chebU 17 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound U17_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,U16_exact,U15_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Boundary.P5.chebU_recurrence x 15
  change Spectral.chebU 17 x=2*x*Spectral.chebU 16 x-Spectral.chebU 15 x at hr
  rw [hr]
  linear_combination he

def U18 : QPoly := ⟨#[-1,0,180,0,-5280,0,59136,0,-329472,0,1025024,0,-1863680,0,1966080,0,-1114112,0,262144]⟩

private theorem U18_checked : polynomialCheck U18
    (((QPoly.constant 2).mul QPoly.X).mul U17 |>.add ((QPoly.constant (-1)).mul U16))=true := by kernel_decide

theorem U18_exact (x : ℝ) : aeval x U18.toPoly=Spectral.chebU 18 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound U18_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,U17_exact,U16_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Boundary.P5.chebU_recurrence x 16
  change Spectral.chebU 18 x=2*x*Spectral.chebU 17 x-Spectral.chebU 16 x at hr
  rw [hr]
  linear_combination he

def U19 : QPoly := ⟨#[0,-20,0,1320,0,-25344,0,219648,0,-1025024,0,2795520,0,-4587520,0,4456448,0,-2359296,0,524288]⟩

private theorem U19_checked : polynomialCheck U19
    (((QPoly.constant 2).mul QPoly.X).mul U18 |>.add ((QPoly.constant (-1)).mul U17))=true := by kernel_decide

theorem U19_exact (x : ℝ) : aeval x U19.toPoly=Spectral.chebU 19 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound U19_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,U18_exact,U17_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Boundary.P5.chebU_recurrence x 17
  change Spectral.chebU 19 x=2*x*Spectral.chebU 18 x-Spectral.chebU 17 x at hr
  rw [hr]
  linear_combination he

def U20 : QPoly := ⟨#[1,0,-220,0,7920,0,-109824,0,768768,0,-3075072,0,7454720,0,-11141120,0,10027008,0,-4980736,0,1048576]⟩

private theorem U20_checked : polynomialCheck U20
    (((QPoly.constant 2).mul QPoly.X).mul U19 |>.add ((QPoly.constant (-1)).mul U18))=true := by kernel_decide

theorem U20_exact (x : ℝ) : aeval x U20.toPoly=Spectral.chebU 20 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound U20_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,U19_exact,U18_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Boundary.P5.chebU_recurrence x 18
  change Spectral.chebU 20 x=2*x*Spectral.chebU 19 x-Spectral.chebU 18 x at hr
  rw [hr]
  linear_combination he

def U21 : QPoly := ⟨#[0,22,0,-1760,0,41184,0,-439296,0,2562560,0,-8945664,0,19496960,0,-26738688,0,22413312,0,-10485760,0,2097152]⟩

private theorem U21_checked : polynomialCheck U21
    (((QPoly.constant 2).mul QPoly.X).mul U20 |>.add ((QPoly.constant (-1)).mul U19))=true := by kernel_decide

theorem U21_exact (x : ℝ) : aeval x U21.toPoly=Spectral.chebU 21 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound U21_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,U20_exact,U19_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Boundary.P5.chebU_recurrence x 19
  change Spectral.chebU 21 x=2*x*Spectral.chebU 20 x-Spectral.chebU 19 x at hr
  rw [hr]
  linear_combination he

def U22 : QPoly := ⟨#[-1,0,264,0,-11440,0,192192,0,-1647360,0,8200192,0,-25346048,0,50135040,0,-63504384,0,49807360,0,-22020096,0,4194304]⟩

private theorem U22_checked : polynomialCheck U22
    (((QPoly.constant 2).mul QPoly.X).mul U21 |>.add ((QPoly.constant (-1)).mul U20))=true := by kernel_decide

theorem U22_exact (x : ℝ) : aeval x U22.toPoly=Spectral.chebU 22 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound U22_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,U21_exact,U20_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Boundary.P5.chebU_recurrence x 20
  change Spectral.chebU 22 x=2*x*Spectral.chebU 21 x-Spectral.chebU 20 x at hr
  rw [hr]
  linear_combination he

def U23 : QPoly := ⟨#[0,-24,0,2288,0,-64064,0,823680,0,-5857280,0,25346048,0,-70189056,0,127008768,0,-149422080,0,110100480,0,-46137344,0,8388608]⟩

private theorem U23_checked : polynomialCheck U23
    (((QPoly.constant 2).mul QPoly.X).mul U22 |>.add ((QPoly.constant (-1)).mul U21))=true := by kernel_decide

theorem U23_exact (x : ℝ) : aeval x U23.toPoly=Spectral.chebU 23 x := by
  have he := congrArg (aeval x) (polynomialCheck_sound U23_checked)
  simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,
    map_add,map_mul,aeval_C,aeval_X,U22_exact,U21_exact] at he
  simp only [map_ofNat,map_neg,map_one] at he
  have hr := Boundary.P5.chebU_recurrence x 21
  change Spectral.chebU 23 x=2*x*Spectral.chebU 22 x-Spectral.chebU 21 x at hr
  rw [hr]
  linear_combination he

def TG00 : QPoly := QPoly.zero
private theorem TG00_checked : polynomialCheck
    (T00.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG00))=true := by kernel_decide

def TX00 : QPoly := QPoly.zero
private theorem TX00_checked : polynomialCheck
    (T00.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TX00))=true := by kernel_decide

def UX00 : QPoly := QPoly.zero
private theorem UX00_checked : polynomialCheck
    (U00.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul UX00))=true := by kernel_decide

def UG00 : QPoly := ⟨#[1]⟩
private theorem UG00_checked : polynomialCheck
    (U00.compose ((QPoly.constant 1).add QPoly.X)) UG00=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag00 : LagCode 0 where
  tCentre := 1
  uCentre := 1
  TGdiv := TG00
  TXdiv := TX00
  UXdiv := UX00
  UG := UG00
  TY := T00
  UY := U00
  TG_exact h := by simpa using shifted_divided_exact T00 T00_exact 1 1 TG00 TG00_checked h
  TX_exact r := by simpa using shifted_divided_exact T00 T00_exact (-1/2) (1) TX00 TX00_checked r
  UX_exact r := by simpa using shifted_divided_exact U00 U00_exact (-1/2) (1) UX00 UX00_checked r
  UG_exact h := by simpa using shifted_exact U00 U00_exact 1 UG00 UG00_checked h
  TY_exact := T00_exact
  UY_exact := U00_exact

def TG01 : QPoly := ⟨#[1]⟩
private theorem TG01_checked : polynomialCheck
    (T01.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG01))=true := by kernel_decide

def TX01 : QPoly := ⟨#[1]⟩
private theorem TX01_checked : polynomialCheck
    (T01.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant ((-1/2))).add (QPoly.X.mul TX01))=true := by kernel_decide

def UX01 : QPoly := QPoly.zero
private theorem UX01_checked : polynomialCheck
    (U00.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul UX01))=true := by kernel_decide

def UG01 : QPoly := ⟨#[1]⟩
private theorem UG01_checked : polynomialCheck
    (U00.compose ((QPoly.constant 1).add QPoly.X)) UG01=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag01 : LagCode 1 where
  tCentre := (-1/2)
  uCentre := 1
  TGdiv := TG01
  TXdiv := TX01
  UXdiv := UX01
  UG := UG01
  TY := T01
  UY := U00
  TG_exact h := by simpa using shifted_divided_exact T01 T01_exact 1 1 TG01 TG01_checked h
  TX_exact r := by simpa using shifted_divided_exact T01 T01_exact (-1/2) ((-1/2)) TX01 TX01_checked r
  UX_exact r := by simpa using shifted_divided_exact U00 U00_exact (-1/2) (1) UX01 UX01_checked r
  UG_exact h := by simpa using shifted_exact U00 U00_exact 1 UG01 UG01_checked h
  TY_exact := T01_exact
  UY_exact := U00_exact

def TG02 : QPoly := ⟨#[4,2]⟩
private theorem TG02_checked : polynomialCheck
    (T02.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG02))=true := by kernel_decide

def TX02 : QPoly := ⟨#[-2,2]⟩
private theorem TX02_checked : polynomialCheck
    (T02.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant ((-1/2))).add (QPoly.X.mul TX02))=true := by kernel_decide

def UX02 : QPoly := ⟨#[2]⟩
private theorem UX02_checked : polynomialCheck
    (U01.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (-1)).add (QPoly.X.mul UX02))=true := by kernel_decide

def UG02 : QPoly := ⟨#[2,2]⟩
private theorem UG02_checked : polynomialCheck
    (U01.compose ((QPoly.constant 1).add QPoly.X)) UG02=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag02 : LagCode 2 where
  tCentre := (-1/2)
  uCentre := -1
  TGdiv := TG02
  TXdiv := TX02
  UXdiv := UX02
  UG := UG02
  TY := T02
  UY := U01
  TG_exact h := by simpa using shifted_divided_exact T02 T02_exact 1 1 TG02 TG02_checked h
  TX_exact r := by simpa using shifted_divided_exact T02 T02_exact (-1/2) ((-1/2)) TX02 TX02_checked r
  UX_exact r := by simpa using shifted_divided_exact U01 U01_exact (-1/2) (-1) UX02 UX02_checked r
  UG_exact h := by simpa using shifted_exact U01 U01_exact 1 UG02 UG02_checked h
  TY_exact := T02_exact
  UY_exact := U01_exact

def TG03 : QPoly := ⟨#[9,12,4]⟩
private theorem TG03_checked : polynomialCheck
    (T03.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG03))=true := by kernel_decide

def TX03 : QPoly := ⟨#[0,-6,4]⟩
private theorem TX03_checked : polynomialCheck
    (T03.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TX03))=true := by kernel_decide

def UX03 : QPoly := ⟨#[-4,4]⟩
private theorem UX03_checked : polynomialCheck
    (U02.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (0)).add (QPoly.X.mul UX03))=true := by kernel_decide

def UG03 : QPoly := ⟨#[3,8,4]⟩
private theorem UG03_checked : polynomialCheck
    (U02.compose ((QPoly.constant 1).add QPoly.X)) UG03=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag03 : LagCode 3 where
  tCentre := 1
  uCentre := 0
  TGdiv := TG03
  TXdiv := TX03
  UXdiv := UX03
  UG := UG03
  TY := T03
  UY := U02
  TG_exact h := by simpa using shifted_divided_exact T03 T03_exact 1 1 TG03 TG03_checked h
  TX_exact r := by simpa using shifted_divided_exact T03 T03_exact (-1/2) (1) TX03 TX03_checked r
  UX_exact r := by simpa using shifted_divided_exact U02 U02_exact (-1/2) (0) UX03 UX03_checked r
  UG_exact h := by simpa using shifted_exact U02 U02_exact 1 UG03 UG03_checked h
  TY_exact := T03_exact
  UY_exact := U02_exact

def TG04 : QPoly := ⟨#[16,40,32,8]⟩
private theorem TG04_checked : polynomialCheck
    (T04.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG04))=true := by kernel_decide

def TX04 : QPoly := ⟨#[4,4,-16,8]⟩
private theorem TX04_checked : polynomialCheck
    (T04.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant ((-1/2))).add (QPoly.X.mul TX04))=true := by kernel_decide

def UX04 : QPoly := ⟨#[2,-12,8]⟩
private theorem UX04_checked : polynomialCheck
    (U03.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul UX04))=true := by kernel_decide

def UG04 : QPoly := ⟨#[4,20,24,8]⟩
private theorem UG04_checked : polynomialCheck
    (U03.compose ((QPoly.constant 1).add QPoly.X)) UG04=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag04 : LagCode 4 where
  tCentre := (-1/2)
  uCentre := 1
  TGdiv := TG04
  TXdiv := TX04
  UXdiv := UX04
  UG := UG04
  TY := T04
  UY := U03
  TG_exact h := by simpa using shifted_divided_exact T04 T04_exact 1 1 TG04 TG04_checked h
  TX_exact r := by simpa using shifted_divided_exact T04 T04_exact (-1/2) ((-1/2)) TX04 TX04_checked r
  UX_exact r := by simpa using shifted_divided_exact U03 U03_exact (-1/2) (1) UX04 UX04_checked r
  UG_exact h := by simpa using shifted_exact U03 U03_exact 1 UG04 UG04_checked h
  TY_exact := T04_exact
  UY_exact := U03_exact

def TG05 : QPoly := ⟨#[25,100,140,80,16]⟩
private theorem TG05_checked : polynomialCheck
    (T05.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG05))=true := by kernel_decide

def TX05 : QPoly := ⟨#[-5,10,20,-40,16]⟩
private theorem TX05_checked : polynomialCheck
    (T05.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant ((-1/2))).add (QPoly.X.mul TX05))=true := by kernel_decide

def UX05 : QPoly := ⟨#[4,12,-32,16]⟩
private theorem UX05_checked : polynomialCheck
    (U04.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (-1)).add (QPoly.X.mul UX05))=true := by kernel_decide

def UG05 : QPoly := ⟨#[5,40,84,64,16]⟩
private theorem UG05_checked : polynomialCheck
    (U04.compose ((QPoly.constant 1).add QPoly.X)) UG05=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag05 : LagCode 5 where
  tCentre := (-1/2)
  uCentre := -1
  TGdiv := TG05
  TXdiv := TX05
  UXdiv := UX05
  UG := UG05
  TY := T05
  UY := U04
  TG_exact h := by simpa using shifted_divided_exact T05 T05_exact 1 1 TG05 TG05_checked h
  TX_exact r := by simpa using shifted_divided_exact T05 T05_exact (-1/2) ((-1/2)) TX05 TX05_checked r
  UX_exact r := by simpa using shifted_divided_exact U04 U04_exact (-1/2) (-1) UX05 UX05_checked r
  UG_exact h := by simpa using shifted_exact U04 U04_exact 1 UG05 UG05_checked h
  TY_exact := T05_exact
  UY_exact := U04_exact

def TG06 : QPoly := ⟨#[36,210,448,432,192,32]⟩
private theorem TG06_checked : polynomialCheck
    (T06.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG06))=true := by kernel_decide

def TX06 : QPoly := ⟨#[0,-24,16,72,-96,32]⟩
private theorem TX06_checked : polynomialCheck
    (T06.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TX06))=true := by kernel_decide

def UX06 : QPoly := ⟨#[-8,8,48,-80,32]⟩
private theorem UX06_checked : polynomialCheck
    (U05.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (0)).add (QPoly.X.mul UX06))=true := by kernel_decide

def UG06 : QPoly := ⟨#[6,70,224,288,160,32]⟩
private theorem UG06_checked : polynomialCheck
    (U05.compose ((QPoly.constant 1).add QPoly.X)) UG06=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag06 : LagCode 6 where
  tCentre := 1
  uCentre := 0
  TGdiv := TG06
  TXdiv := TX06
  UXdiv := UX06
  UG := UG06
  TY := T06
  UY := U05
  TG_exact h := by simpa using shifted_divided_exact T06 T06_exact 1 1 TG06 TG06_checked h
  TX_exact r := by simpa using shifted_divided_exact T06 T06_exact (-1/2) (1) TX06 TX06_checked r
  UX_exact r := by simpa using shifted_divided_exact U05 U05_exact (-1/2) (0) UX06 UX06_checked r
  UG_exact h := by simpa using shifted_exact U05 U05_exact 1 UG06 UG06_checked h
  TY_exact := T06_exact
  UY_exact := U05_exact

def TG07 : QPoly := ⟨#[49,392,1176,1680,1232,448,64]⟩
private theorem TG07_checked : polynomialCheck
    (T07.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG07))=true := by kernel_decide

def TX07 : QPoly := ⟨#[7,14,-84,0,224,-224,64]⟩
private theorem TX07_checked : polynomialCheck
    (T07.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant ((-1/2))).add (QPoly.X.mul TX07))=true := by kernel_decide

def UX07 : QPoly := ⟨#[4,-36,0,160,-192,64]⟩
private theorem UX07_checked : polynomialCheck
    (U06.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul UX07))=true := by kernel_decide

def UG07 : QPoly := ⟨#[7,112,504,960,880,384,64]⟩
private theorem UG07_checked : polynomialCheck
    (U06.compose ((QPoly.constant 1).add QPoly.X)) UG07=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag07 : LagCode 7 where
  tCentre := (-1/2)
  uCentre := 1
  TGdiv := TG07
  TXdiv := TX07
  UXdiv := UX07
  UG := UG07
  TY := T07
  UY := U06
  TG_exact h := by simpa using shifted_divided_exact T07 T07_exact 1 1 TG07 TG07_checked h
  TX_exact r := by simpa using shifted_divided_exact T07 T07_exact (-1/2) ((-1/2)) TX07 TX07_checked r
  UX_exact r := by simpa using shifted_divided_exact U06 U06_exact (-1/2) (1) UX07 UX07_checked r
  UG_exact h := by simpa using shifted_exact U06 U06_exact 1 UG07 UG07_checked h
  TY_exact := T07_exact
  UY_exact := U06_exact

def TG08 : QPoly := ⟨#[64,672,2688,5280,5632,3328,1024,128]⟩
private theorem TG08_checked : polynomialCheck
    (T08.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG08))=true := by kernel_decide

def TX08 : QPoly := ⟨#[-8,24,96,-240,-128,640,-512,128]⟩
private theorem TX08_checked : polynomialCheck
    (T08.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant ((-1/2))).add (QPoly.X.mul TX08))=true := by kernel_decide

def UX08 : QPoly := ⟨#[6,36,-120,-80,480,-448,128]⟩
private theorem UX08_checked : polynomialCheck
    (U07.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (-1)).add (QPoly.X.mul UX08))=true := by kernel_decide

def UG08 : QPoly := ⟨#[8,168,1008,2640,3520,2496,896,128]⟩
private theorem UG08_checked : polynomialCheck
    (U07.compose ((QPoly.constant 1).add QPoly.X)) UG08=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag08 : LagCode 8 where
  tCentre := (-1/2)
  uCentre := -1
  TGdiv := TG08
  TXdiv := TX08
  UXdiv := UX08
  UG := UG08
  TY := T08
  UY := U07
  TG_exact h := by simpa using shifted_divided_exact T08 T08_exact 1 1 TG08 TG08_checked h
  TX_exact r := by simpa using shifted_divided_exact T08 T08_exact (-1/2) ((-1/2)) TX08 TX08_checked r
  UX_exact r := by simpa using shifted_divided_exact U07 U07_exact (-1/2) (-1) UX08 UX08_checked r
  UG_exact h := by simpa using shifted_exact U07 U07_exact 1 UG08 UG08_checked h
  TY_exact := T08_exact
  UY_exact := U07_exact

def TG09 : QPoly := ⟨#[81,1080,5544,14256,20592,17472,8640,2304,256]⟩
private theorem TG09_checked : polynomialCheck
    (T09.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG09))=true := by kernel_decide

def TX09 : QPoly := ⟨#[0,-54,36,432,-576,-672,1728,-1152,256]⟩
private theorem TX09_checked : polynomialCheck
    (T09.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TX09))=true := by kernel_decide

def UX09 : QPoly := ⟨#[-12,12,192,-320,-448,1344,-1024,256]⟩
private theorem UX09_checked : polynomialCheck
    (U08.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (0)).add (QPoly.X.mul UX09))=true := by kernel_decide

def UG09 : QPoly := ⟨#[9,240,1848,6336,11440,11648,6720,2048,256]⟩
private theorem UG09_checked : polynomialCheck
    (U08.compose ((QPoly.constant 1).add QPoly.X)) UG09=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag09 : LagCode 9 where
  tCentre := 1
  uCentre := 0
  TGdiv := TG09
  TXdiv := TX09
  UXdiv := UX09
  UG := UG09
  TY := T09
  UY := U08
  TG_exact h := by simpa using shifted_divided_exact T09 T09_exact 1 1 TG09 TG09_checked h
  TX_exact r := by simpa using shifted_divided_exact T09 T09_exact (-1/2) (1) TX09 TX09_checked r
  UX_exact r := by simpa using shifted_divided_exact U08 U08_exact (-1/2) (0) UX09 UX09_checked r
  UG_exact h := by simpa using shifted_exact U08 U08_exact 1 UG09 UG09_checked h
  TY_exact := T09_exact
  UY_exact := U08_exact

def TG10 : QPoly := ⟨#[100,1650,10560,34320,64064,72800,51200,21760,5120,512]⟩
private theorem TG10_checked : polynomialCheck
    (T10.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG10))=true := by kernel_decide

def TX10 : QPoly := ⟨#[10,30,-240,-120,1568,-1120,-2560,4480,-2560,512]⟩
private theorem TX10_checked : polynomialCheck
    (T10.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant ((-1/2))).add (QPoly.X.mul TX10))=true := by kernel_decide

def UX10 : QPoly := ⟨#[6,-72,-48,784,-672,-1792,3584,-2304,512]⟩
private theorem UX10_checked : polynomialCheck
    (U09.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul UX10))=true := by kernel_decide

def UG10 : QPoly := ⟨#[10,330,3168,13728,32032,43680,35840,17408,4608,512]⟩
private theorem UG10_checked : polynomialCheck
    (U09.compose ((QPoly.constant 1).add QPoly.X)) UG10=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag10 : LagCode 10 where
  tCentre := (-1/2)
  uCentre := 1
  TGdiv := TG10
  TXdiv := TX10
  UXdiv := UX10
  UG := UG10
  TY := T10
  UY := U09
  TG_exact h := by simpa using shifted_divided_exact T10 T10_exact 1 1 TG10 TG10_checked h
  TX_exact r := by simpa using shifted_divided_exact T10 T10_exact (-1/2) ((-1/2)) TX10 TX10_checked r
  UX_exact r := by simpa using shifted_divided_exact U09 U09_exact (-1/2) (1) UX10 UX10_checked r
  UG_exact h := by simpa using shifted_exact U09 U09_exact 1 UG10 UG10_checked h
  TY_exact := T10_exact
  UY_exact := U09_exact

def TG11 : QPoly := ⟨#[121,2420,18876,75504,176176,256256,239360,143616,53504,11264,1024]⟩
private theorem TG11_checked : polynomialCheck
    (T11.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG11))=true := by kernel_decide

def TX11 : QPoly := ⟨#[-11,44,264,-792,-1232,4928,-1408,-8448,11264,-5632,1024]⟩
private theorem TX11_checked : polynomialCheck
    (T11.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant ((-1/2))).add (QPoly.X.mul TX11))=true := by kernel_decide

def UX11 : QPoly := ⟨#[8,72,-288,-560,2688,-896,-6144,9216,-5120,1024]⟩
private theorem UX11_checked : polynomialCheck
    (U10.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (-1)).add (QPoly.X.mul UX11))=true := by kernel_decide

def UG11 : QPoly := ⟨#[11,440,5148,27456,80080,139776,152320,104448,43776,10240,1024]⟩
private theorem UG11_checked : polynomialCheck
    (U10.compose ((QPoly.constant 1).add QPoly.X)) UG11=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag11 : LagCode 11 where
  tCentre := (-1/2)
  uCentre := -1
  TGdiv := TG11
  TXdiv := TX11
  UXdiv := UX11
  UG := UG11
  TY := T11
  UY := U10
  TG_exact h := by simpa using shifted_divided_exact T11 T11_exact 1 1 TG11 TG11_checked h
  TX_exact r := by simpa using shifted_divided_exact T11 T11_exact (-1/2) ((-1/2)) TX11 TX11_checked r
  UX_exact r := by simpa using shifted_divided_exact U10 U10_exact (-1/2) (-1) UX11 UX11_checked r
  UG_exact h := by simpa using shifted_exact U10 U10_exact 1 UG11 UG11_checked h
  TY_exact := T11_exact
  UY_exact := U10_exact

def TG12 : QPoly := ⟨#[144,3432,32032,154440,439296,792064,940032,744192,389120,129024,24576,2048]⟩
private theorem TG12_checked : polynomialCheck
    (T12.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG12))=true := by kernel_decide

def TX12 : QPoly := ⟨#[0,-96,64,1440,-1920,-6272,13824,1152,-25600,27648,-12288,2048]⟩
private theorem TX12_checked : polynomialCheck
    (T12.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TX12))=true := by kernel_decide

def UX12 : QPoly := ⟨#[-16,16,480,-800,-3136,8064,768,-19200,23040,-11264,2048]⟩
private theorem UX12_checked : polynomialCheck
    (U11.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (0)).add (QPoly.X.mul UX12))=true := by kernel_decide

def UG12 : QPoly := ⟨#[12,572,8008,51480,183040,396032,548352,496128,291840,107520,22528,2048]⟩
private theorem UG12_checked : polynomialCheck
    (U11.compose ((QPoly.constant 1).add QPoly.X)) UG12=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag12 : LagCode 12 where
  tCentre := 1
  uCentre := 0
  TGdiv := TG12
  TXdiv := TX12
  UXdiv := UX12
  UG := UG12
  TY := T12
  UY := U11
  TG_exact h := by simpa using shifted_divided_exact T12 T12_exact 1 1 TG12 TG12_checked h
  TX_exact r := by simpa using shifted_divided_exact T12 T12_exact (-1/2) (1) TX12 TX12_checked r
  UX_exact r := by simpa using shifted_divided_exact U11 U11_exact (-1/2) (0) UX12 UX12_checked r
  UG_exact h := by simpa using shifted_exact U11 U11_exact 1 UG12 UG12_checked h
  TY_exact := T12_exact
  UY_exact := U11_exact

def TG13 : QPoly := ⟨#[169,4732,52052,297440,1011296,2206464,3224832,3224832,2213120,1025024,306176,53248,4096]⟩
private theorem TG13_checked : polynomialCheck
    (T13.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG13))=true := by kernel_decide

def TX13 : QPoly := ⟨#[13,52,-520,-520,6032,-2496,-24960,34944,16640,-73216,66560,-26624,4096]⟩
private theorem TX13_checked : polynomialCheck
    (T13.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant ((-1/2))).add (QPoly.X.mul TX13))=true := by kernel_decide

def UX13 : QPoly := ⟨#[8,-120,-160,2320,-1152,-13440,21504,11520,-56320,56320,-24576,4096]⟩
private theorem UX13_checked : polynomialCheck
    (U12.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul UX13))=true := by kernel_decide

def UG13 : QPoly := ⟨#[13,728,12012,91520,388960,1018368,1736448,1984512,1532160,788480,259072,49152,4096]⟩
private theorem UG13_checked : polynomialCheck
    (U12.compose ((QPoly.constant 1).add QPoly.X)) UG13=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag13 : LagCode 13 where
  tCentre := (-1/2)
  uCentre := 1
  TGdiv := TG13
  TXdiv := TX13
  UXdiv := UX13
  UG := UG13
  TY := T13
  UY := U12
  TG_exact h := by simpa using shifted_divided_exact T13 T13_exact 1 1 TG13 TG13_checked h
  TX_exact r := by simpa using shifted_divided_exact T13 T13_exact (-1/2) ((-1/2)) TX13 TX13_checked r
  UX_exact r := by simpa using shifted_divided_exact U12 U12_exact (-1/2) (1) UX13 UX13_checked r
  UG_exact h := by simpa using shifted_exact U12 U12_exact 1 UG13 UG13_checked h
  TY_exact := T13_exact
  UY_exact := U12_exact

def TG14 : QPoly := ⟨#[196,6370,81536,544544,2178176,5643456,9922560,12155136,10486784,6347264,2637824,716800,114688,8192]⟩
private theorem TG14_checked : polynomialCheck
    (T14.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG14))=true := by kernel_decide

def TX14 : QPoly := ⟨#[-14,70,560,-1960,-5152,20832,6144,-86016,78848,78848,-200704,157696,-57344,8192]⟩
private theorem TX14_checked : polynomialCheck
    (T14.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant ((-1/2))).add (QPoly.X.mul TX14))=true := by kernel_decide

def UX14 : QPoly := ⟨#[10,120,-560,-1840,8928,3072,-49152,50688,56320,-157696,135168,-53248,8192]⟩
private theorem UX14_checked : polynomialCheck
    (U13.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (-1)).add (QPoly.X.mul UX14))=true := by kernel_decide

def UG14 : QPoly := ⟨#[14,910,17472,155584,777920,2418624,4961280,6945792,6741504,4533760,2072576,614400,106496,8192]⟩
private theorem UG14_checked : polynomialCheck
    (U13.compose ((QPoly.constant 1).add QPoly.X)) UG14=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag14 : LagCode 14 where
  tCentre := (-1/2)
  uCentre := -1
  TGdiv := TG14
  TXdiv := TX14
  UXdiv := UX14
  UG := UG14
  TY := T14
  UY := U13
  TG_exact h := by simpa using shifted_divided_exact T14 T14_exact 1 1 TG14 TG14_checked h
  TX_exact r := by simpa using shifted_divided_exact T14 T14_exact (-1/2) ((-1/2)) TX14 TX14_checked r
  UX_exact r := by simpa using shifted_divided_exact U13 U13_exact (-1/2) (-1) UX14 UX14_checked r
  UG_exact h := by simpa using shifted_exact U13 U13_exact 1 UG14 UG14_checked h
  TY_exact := T14_exact
  UY_exact := U13_exact

def TG15 : QPoly := ⟨#[225,8400,123760,954720,4434144,13436800,27907200,40930560,43070720,32643072,17664000,6656000,1658880,245760,16384]⟩
private theorem TG15_checked : polynomialCheck
    (T15.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG15))=true := by kernel_decide

def TX15 : QPoly := ⟨#[0,-150,100,3600,-4800,-28640,60480,63360,-267520,152064,291840,-532480,368640,-122880,16384]⟩
private theorem TX15_checked : polynomialCheck
    (T15.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TX15))=true := by kernel_decide

def UX15 : QPoly := ⟨#[-20,20,960,-1600,-11456,28224,33792,-160512,101376,214016,-425984,319488,-114688,16384]⟩
private theorem UX15_checked : polynomialCheck
    (U14.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (0)).add (QPoly.X.mul UX15))=true := by kernel_decide

def UG15 : QPoly := ⟨#[15,1120,24752,254592,1478048,5374720,13023360,21829632,25842432,21762048,12953600,5324800,1437696,229376,16384]⟩
private theorem UG15_checked : polynomialCheck
    (U14.compose ((QPoly.constant 1).add QPoly.X)) UG15=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag15 : LagCode 15 where
  tCentre := 1
  uCentre := 0
  TGdiv := TG15
  TXdiv := TX15
  UXdiv := UX15
  UG := UG15
  TY := T15
  UY := U14
  TG_exact h := by simpa using shifted_divided_exact T15 T15_exact 1 1 TG15 TG15_checked h
  TX_exact r := by simpa using shifted_divided_exact T15 T15_exact (-1/2) (1) TX15 TX15_checked r
  UX_exact r := by simpa using shifted_divided_exact U14 U14_exact (-1/2) (0) UX15 UX15_checked r
  UG_exact h := by simpa using shifted_exact U14 U14_exact 1 UG15 UG15_checked h
  TY_exact := T15_exact
  UY_exact := U14_exact

def TG16 : QPoly := ⟨#[256,10880,182784,1612416,8599552,30098432,72765440,125520384,157515776,145080320,97976320,47923200,16515072,3801088,524288,32768]⟩
private theorem TG16_checked : polynomialCheck
    (T16.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG16))=true := by kernel_decide

def TX16 : QPoly := ⟨#[16,80,-960,-1440,17152,-1792,-123904,143616,315392,-765952,212992,958464,-1376256,851968,-262144,32768]⟩
private theorem TX16_checked : polynomialCheck
    (T16.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant ((-1/2))).add (QPoly.X.mul TX16))=true := by kernel_decide

def UX16 : QPoly := ⟨#[10,-180,-360,5360,-672,-54208,71808,177408,-478720,146432,718848,-1118208,745472,-245760,32768]⟩
private theorem UX16_checked : polynomialCheck
    (U15.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul UX16))=true := by kernel_decide

def UG16 : QPoly := ⟨#[16,1360,34272,403104,2687360,11286912,31834880,62760192,88602624,90675200,67358720,35942400,13418496,3325952,491520,32768]⟩
private theorem UG16_checked : polynomialCheck
    (U15.compose ((QPoly.constant 1).add QPoly.X)) UG16=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag16 : LagCode 16 where
  tCentre := (-1/2)
  uCentre := 1
  TGdiv := TG16
  TXdiv := TX16
  UXdiv := UX16
  UG := UG16
  TY := T16
  UY := U15
  TG_exact h := by simpa using shifted_divided_exact T16 T16_exact 1 1 TG16 TG16_checked h
  TX_exact r := by simpa using shifted_divided_exact T16 T16_exact (-1/2) ((-1/2)) TX16 TX16_checked r
  UX_exact r := by simpa using shifted_divided_exact U15 U15_exact (-1/2) (1) UX16 UX16_checked r
  UG_exact h := by simpa using shifted_exact U15 U15_exact 1 UG16 UG16_checked h
  TY_exact := T16_exact
  UY_exact := U15_exact

def TG17 : QPoly := ⟨#[289,13872,263568,2635680,15989792,63959168,177820544,355641088,523001600,572549120,468449280,285143040,127217664,40386560,8634368,1114112,65536]⟩
private theorem TG17_checked : polynomialCheck
    (T17.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG17))=true := by kernel_decide

def TX17 : QPoly := ⟨#[-17,102,1020,-4080,-15232,64736,59840,-454784,239360,1244672,-2036736,0,2924544,-3481600,1949696,-557056,65536]⟩
private theorem TX17_checked : polynomialCheck
    (T17.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant ((-1/2))).add (QPoly.X.mul TX17))=true := by kernel_decide

def UX17 : QPoly := ⟨#[12,180,-960,-4480,22848,24640,-214016,126720,732160,-1317888,0,2236416,-2867200,1720320,-524288,65536]⟩
private theorem UX17_checked : polynomialCheck
    (U16.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (-1)).add (QPoly.X.mul UX17))=true := by kernel_decide

def UG17 : QPoly := ⟨#[17,1632,46512,620160,4702880,22573824,73220224,167360512,276883200,336793600,303114240,201277440,97284096,33259520,7618560,1048576,65536]⟩
private theorem UG17_checked : polynomialCheck
    (U16.compose ((QPoly.constant 1).add QPoly.X)) UG17=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag17 : LagCode 17 where
  tCentre := (-1/2)
  uCentre := -1
  TGdiv := TG17
  TXdiv := TX17
  UXdiv := UX17
  UG := UG17
  TY := T17
  UY := U16
  TG_exact h := by simpa using shifted_divided_exact T17 T17_exact 1 1 TG17 TG17_checked h
  TX_exact r := by simpa using shifted_divided_exact T17 T17_exact (-1/2) ((-1/2)) TX17 TX17_checked r
  UX_exact r := by simpa using shifted_divided_exact U16 U16_exact (-1/2) (-1) UX17 UX17_checked r
  UG_exact h := by simpa using shifted_exact U16 U16_exact 1 UG17 UG17_checked h
  TY_exact := T17_exact
  UY_exact := U16_exact

def TG18 : QPoly := ⟨#[324,17442,372096,4186080,28651392,129799488,410793984,941402880,1599769600,2046021120,1984020480,1459261440,808206336,331407360,97517568,19464192,2359296,131072]⟩
private theorem TG18_checked : polynomialCheck
    (T18.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG18))=true := by kernel_decide

def TX18 : QPoly := ⟨#[0,-216,144,7560,-10080,-93408,193536,430848,-1464320,0,4313088,-5031936,-1548288,8478720,-8650752,4423680,-1179648,131072]⟩
private theorem TX18_checked : polynomialCheck
    (T18.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TX18))=true := by kernel_decide

def UX18 : QPoly := ⟨#[-24,24,1680,-2800,-31136,75264,191488,-732160,0,2635776,-3354624,-1118208,6594560,-7208960,3932160,-1114112,131072]⟩
private theorem UX18_checked : polynomialCheck
    (U17.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (0)).add (QPoly.X.mul UX18))=true := by kernel_decide

def UG18 : QPoly := ⟨#[18,1938,62016,930240,7958720,43266496,159753216,418401280,799884800,1136678400,1212456960,972840960,583704576,257761280,81264640,17301504,2228224,131072]⟩
private theorem UG18_checked : polynomialCheck
    (U17.compose ((QPoly.constant 1).add QPoly.X)) UG18=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag18 : LagCode 18 where
  tCentre := 1
  uCentre := 0
  TGdiv := TG18
  TXdiv := TX18
  UXdiv := UX18
  UG := UG18
  TY := T18
  UY := U17
  TG_exact h := by simpa using shifted_divided_exact T18 T18_exact 1 1 TG18 TG18_checked h
  TX_exact r := by simpa using shifted_divided_exact T18 T18_exact (-1/2) (1) TX18 TX18_checked r
  UX_exact r := by simpa using shifted_divided_exact U17 U17_exact (-1/2) (0) UX18 UX18_checked r
  UG_exact h := by simpa using shifted_exact U17 U17_exact 1 UG18 UG18_checked h
  TY_exact := T18_exact
  UY_exact := U17_exact

def TG19 : QPoly := ⟨#[361,21660,515508,6480672,49685152,252942592,903366400,2348752640,4559343360,6719032320,7591633920,6601420800,4407717888,2238840832,849215488,232849408,43581440,4980736,262144]⟩
private theorem TG19_checked : polynomialCheck
    (T19.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG19))=true := by kernel_decide

def TX19 : QPoly := ⟨#[19,114,-1596,-3192,40432,8512,-440192,411008,2086656,-4173312,-2276352,13658112,-11440128,-8093696,23658496,-21168128,9961472,-2490368,262144]⟩
private theorem TX19_checked : polynomialCheck
    (T19.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant ((-1/2))).add (QPoly.X.mul TX19))=true := by kernel_decide

def UX19 : QPoly := ⟨#[12,-252,-672,10640,2688,-162176,173056,988416,-2196480,-1317888,8626176,-7827456,-5963776,18677760,-17825792,8912896,-2359296,262144]⟩
private theorem UX19_checked : polynomialCheck
    (U18.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul UX19))=true := by kernel_decide

def UG19 : QPoly := ⟨#[19,2280,81396,1364352,13075040,79876608,332819200,988948480,2159688960,3536332800,4395156480,4169318400,3015806976,1649672192,670433280,196083712,38993920,4718592,262144]⟩
private theorem UG19_checked : polynomialCheck
    (U18.compose ((QPoly.constant 1).add QPoly.X)) UG19=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag19 : LagCode 19 where
  tCentre := (-1/2)
  uCentre := 1
  TGdiv := TG19
  TXdiv := TX19
  UXdiv := UX19
  UG := UG19
  TY := T19
  UY := U18
  TG_exact h := by simpa using shifted_divided_exact T19 T19_exact 1 1 TG19 TG19_checked h
  TX_exact r := by simpa using shifted_divided_exact T19 T19_exact (-1/2) ((-1/2)) TX19 TX19_checked r
  UX_exact r := by simpa using shifted_divided_exact U18 U18_exact (-1/2) (1) UX19 UX19_checked r
  UG_exact h := by simpa using shifted_exact U18 U18_exact 1 UG19 UG19_checked h
  TY_exact := T19_exact
  UY_exact := U18_exact

def TG20 : QPoly := ⟨#[400,26600,702240,9806280,83680256,475456000,1901824000,5562835200,12216422400,20510730240,26637312000,26926848000,21210071040,12961710080,6078595072,2144665600,550502400,96993280,10485760,524288]⟩
private theorem TG20_checked : polynomialCheck
    (T20.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG20))=true := by kernel_decide

def TX20 : QPoly := ⟨#[-20,140,1680,-7560,-36736,165760,263680,-1722240,199680,8346624,-10383360,-13178880,40304640,-23265280,-31195136,64061440,-51118080,22282240,-5242880,524288]⟩
private theorem TX20_checked : polynomialCheck
    (T20.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant ((-1/2))).add (QPoly.X.mul TX20))=true := by kernel_decide

def UX20 : QPoly := ⟨#[14,252,-1512,-9184,49728,92288,-688896,89856,4173312,-5710848,-7907328,26198016,-16285696,-23396352,51249152,-43450368,20054016,-4980736,524288]⟩
private theorem UX20_checked : polynomialCheck
    (U19.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (-1)).add (QPoly.X.mul UX20))=true := by kernel_decide

def UG20 : QPoly := ⟨#[20,2660,105336,1961256,20920064,142636800,665638400,2225134080,5497390080,10255365120,14650521600,16156108800,13786546176,9073197056,4558946304,1715732480,467927040,87293952,9961472,524288]⟩
private theorem UG20_checked : polynomialCheck
    (U19.compose ((QPoly.constant 1).add QPoly.X)) UG20=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag20 : LagCode 20 where
  tCentre := (-1/2)
  uCentre := -1
  TGdiv := TG20
  TXdiv := TX20
  UXdiv := UX20
  UG := UG20
  TY := T20
  UY := U19
  TG_exact h := by simpa using shifted_divided_exact T20 T20_exact 1 1 TG20 TG20_checked h
  TX_exact r := by simpa using shifted_divided_exact T20 T20_exact (-1/2) ((-1/2)) TX20 TX20_checked r
  UX_exact r := by simpa using shifted_divided_exact U19 U19_exact (-1/2) (-1) UX20 UX20_checked r
  UG_exact h := by simpa using shifted_exact U19 U19_exact 1 UG20 UG20_checked h
  TY_exact := T20_exact
  UY_exact := U19_exact

def TG21 : QPoly := ⟨#[441,32340,942172,14536368,137287920,865329920,3851193600,12580565760,30999171840,58735272960,86704450560,100526899200,91866120192,66104721408,37231394816,16213671936,5346754560,1290010624,214695936,22020096,1048576]⟩
private theorem TG21_checked : polynomialCheck
    (T21.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG21))=true := by kernel_decide

def TX21 : QPoly := ⟨#[0,-294,196,14112,-18816,-247744,508032,1838592,-5730816,-3773952,29352960,-21245952,-55222272,111968256,-38993920,-105283584,169279488,-122028032,49545216,-11010048,1048576]⟩
private theorem TX21_checked : polynomialCheck
    (T21.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TX21))=true := by kernel_decide

def UX21 : QPoly := ⟨#[-28,28,2688,-4480,-70784,169344,700416,-2456064,-1797120,15375360,-12140544,-34185216,74645504,-27852800,-80216064,137035776,-104595456,44826624,-10485760,1048576]⟩
private theorem UX21_checked : polynomialCheck
    (U20.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (0)).add (QPoly.X.mul UX21))=true := by kernel_decide

def UG21 : QPoly := ⟨#[21,3080,134596,2768832,32687600,247237120,1283731200,4792596480,13285359360,27969177600,45416616960,57443942400,56869502976,44069814272,26593853440,12353273856,4328325120,1105723392,194248704,20971520,1048576]⟩
private theorem UG21_checked : polynomialCheck
    (U20.compose ((QPoly.constant 1).add QPoly.X)) UG21=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag21 : LagCode 21 where
  tCentre := 1
  uCentre := 0
  TGdiv := TG21
  TXdiv := TX21
  UXdiv := UX21
  UG := UG21
  TY := T21
  UY := U20
  TG_exact h := by simpa using shifted_divided_exact T21 T21_exact 1 1 TG21 TG21_checked h
  TX_exact r := by simpa using shifted_divided_exact T21 T21_exact (-1/2) (1) TX21 TX21_checked r
  UX_exact r := by simpa using shifted_divided_exact U20 U20_exact (-1/2) (0) UX21 UX21_checked r
  UG_exact h := by simpa using shifted_exact U20 U20_exact 1 UG21 UG21_checked h
  TY_exact := T21_exact
  UY_exact := U20_exact

def TG22 : QPoly := ⟨#[484,38962,1246784,21150800,219968320,1529779680,7531223040,27300683520,74943052800,158958159360,264242135040,347535851520,363575967744,302979973120,200593637376,104745467904,42570350592,13176537088,2998927360,472907776,46137344,2097152]⟩
private theorem TG22_checked : polynomialCheck
    (T22.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG22))=true := by kernel_decide

def TX22 : QPoly := ⟨#[22,154,-2464,-6160,83776,44352,-1267200,899712,9208320,-16034304,-26517504,93130752,-27574272,-199147520,294125568,-36765696,-328728576,438304768,-288358400,109576192,-23068672,2097152]⟩
private theorem TX22_checked : polynomialCheck
    (T22.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant ((-1/2))).add (QPoly.X.mul TX22))=true := by kernel_decide

def UX22 : QPoly := ⟨#[14,-336,-1120,19040,12096,-403200,327168,3767040,-7288320,-13258752,50798592,-16293888,-126730240,200540160,-26738688,-254017536,358612992,-249036800,99614720,-22020096,2097152]⟩
private theorem UX22_checked : polynomialCheck
    (U21.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul UX22))=true := by kernel_decide

def UG22 : QPoly := ⟨#[22,3542,170016,3845600,49992800,417212640,2396298240,9927521280,30658521600,72253708800,132121067520,189565009920,214840344576,192805437440,136768389120,76178522112,32895270912,10780803072,2589982720,429916160,44040192,2097152]⟩
private theorem UG22_checked : polynomialCheck
    (U21.compose ((QPoly.constant 1).add QPoly.X)) UG22=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag22 : LagCode 22 where
  tCentre := (-1/2)
  uCentre := 1
  TGdiv := TG22
  TXdiv := TX22
  UXdiv := UX22
  UG := UG22
  TY := T22
  UY := U21
  TG_exact h := by simpa using shifted_divided_exact T22 T22_exact 1 1 TG22 TG22_checked h
  TX_exact r := by simpa using shifted_divided_exact T22 T22_exact (-1/2) ((-1/2)) TX22 TX22_checked r
  UX_exact r := by simpa using shifted_divided_exact U21 U21_exact (-1/2) (1) UX22 UX22_checked r
  UG_exact h := by simpa using shifted_exact U21 U21_exact 1 UG22 UG22_checked h
  TY_exact := T22_exact
  UY_exact := U21_exact

def TG23 : QPoly := ⟨#[529,46552,1629320,30258800,344950320,2634166080,14270811840,57083247360,173488300800,409067151360,759696138240,1123029073920,1330357518336,1267007160320,969915826176,594464538624,289284882432,110203764736,32136232960,6921650176,1037041664,96468992,4194304]⟩
private theorem TG23_checked : polynomialCheck
    (T23.compose ((QPoly.constant (1)).add QPoly.X))
    ((QPoly.constant (1)).add (QPoly.X.mul TG23))=true := by kernel_decide

def TX23 : QPoly := ⟨#[-23,184,2576,-12880,-77280,370944,847872,-5272704,-1678080,38224896,-34904064,-124919808,269058048,32030720,-653426688,730300416,85917696,-973733888,1115422720,-675282944,241172480,-48234496,4194304]⟩
private theorem TX23_checked : polynomialCheck
    (T23.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant ((-1/2))).add (QPoly.X.mul TX23))=true := by kernel_decide

def UX23 : QPoly := ⟨#[16,336,-2240,-16800,96768,258048,-1833984,-656640,16619520,-16693248,-65175552,152076288,19496960,-426147840,508035072,63504384,-762052608,921436160,-587202560,220200960,-46137344,4194304]⟩
private theorem UX23_checked : polynomialCheck
    (U22.compose ((QPoly.constant ((-1/2))).add QPoly.X))
    ((QPoly.constant (-1)).add (QPoly.X.mul UX23))=true := by kernel_decide

def UG23 : QPoly := ⟨#[23,4048,212520,5262400,74989200,687173760,4343290560,19855042560,67886726400,177855283200,363332935680,585928212480,751941206016,771221749760,632553799680,413540548608,213819260928,86246424576,26547322880,6018826240,946864128,92274688,4194304]⟩
private theorem UG23_checked : polynomialCheck
    (U22.compose ((QPoly.constant 1).add QPoly.X)) UG23=true := by kernel_decide

/-- Concrete polynomial data linked to all six actual lag functions. -/
def lag23 : LagCode 23 where
  tCentre := (-1/2)
  uCentre := -1
  TGdiv := TG23
  TXdiv := TX23
  UXdiv := UX23
  UG := UG23
  TY := T23
  UY := U22
  TG_exact h := by simpa using shifted_divided_exact T23 T23_exact 1 1 TG23 TG23_checked h
  TX_exact r := by simpa using shifted_divided_exact T23 T23_exact (-1/2) ((-1/2)) TX23 TX23_checked r
  UX_exact r := by simpa using shifted_divided_exact U22 U22_exact (-1/2) (-1) UX23 UX23_checked r
  UG_exact h := by simpa using shifted_exact U22 U22_exact 1 UG23 UG23_checked h
  TY_exact := T23_exact
  UY_exact := U22_exact

def codes : (n : Fin 24) → LagCode n
  | ⟨0,_⟩ => lag00
  | ⟨1,_⟩ => lag01
  | ⟨2,_⟩ => lag02
  | ⟨3,_⟩ => lag03
  | ⟨4,_⟩ => lag04
  | ⟨5,_⟩ => lag05
  | ⟨6,_⟩ => lag06
  | ⟨7,_⟩ => lag07
  | ⟨8,_⟩ => lag08
  | ⟨9,_⟩ => lag09
  | ⟨10,_⟩ => lag10
  | ⟨11,_⟩ => lag11
  | ⟨12,_⟩ => lag12
  | ⟨13,_⟩ => lag13
  | ⟨14,_⟩ => lag14
  | ⟨15,_⟩ => lag15
  | ⟨16,_⟩ => lag16
  | ⟨17,_⟩ => lag17
  | ⟨18,_⟩ => lag18
  | ⟨19,_⟩ => lag19
  | ⟨20,_⟩ => lag20
  | ⟨21,_⟩ => lag21
  | ⟨22,_⟩ => lag22
  | ⟨23,_⟩ => lag23
  | ⟨n+24,h⟩ => False.elim (by omega)

end polyak.Certificates.Continuation.P5Lags
