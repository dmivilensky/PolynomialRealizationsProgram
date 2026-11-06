import polyak.Functions.Normalization
import polyak.Interpolation.Data

/-! Direct source-facing names for equations psi and TR. These are the
existing Polyak definitions and proved gradient formulas, reused literally. -/
namespace nesterov.Spectral
noncomputable section

abbrev normalizeFunction := @polyak.normalizeFunction
abbrev denormalizeFunction := @polyak.denormalizeFunction
abbrev hasGradientAt_normalize := @polyak.hasGradientAt_normalize
abbrev hasGradientAt_denormalize := @polyak.hasGradientAt_denormalize
abbrev datumT := @polyak.Interpolation.datumT
abbrev datumR := @polyak.Interpolation.datumR

end
end nesterov.Spectral
