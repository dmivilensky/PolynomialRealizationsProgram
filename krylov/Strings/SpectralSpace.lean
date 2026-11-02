import krylov.Strings.Mass
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Article: main_krylov, thm:value, Neumann string Hilbert spaces.
Use: the actual mass L² space and physical-gradient L² space used by the
string's energy form and bounded Neumann resolvent.
Source: mathlib L² spaces and the Hilbert L² product.
-/

namespace krylov.Strings.Spectral
noncomputable section
open Set MeasureTheory

abbrev MassHilbert (M : Mass) := Lp ℂ 2 M.measure

abbrev GradientHilbert := Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))

abbrev EnergyAmbient (M : Mass) := WithLp 2 (MassHilbert M × GradientHilbert)

end
end krylov.Strings.Spectral
