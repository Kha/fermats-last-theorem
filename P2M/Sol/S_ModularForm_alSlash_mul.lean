import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
namespace P2MW.S_ModularForm_alSlash_mul

open UpperHalfPlane

theorem solution {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) (k₁ k₂ : ℤ) (F G : ℍ → ℂ) : ModularForm.alSlash W (k₁ + k₂) (F * G) = (q : ℂ) • (ModularForm.alSlash W k₁ F * ModularForm.alSlash W k₂ G) := by
  simp only [ModularForm.alSlash_def, ModularForm.mul_slash, W.val_det_alGL, Nat.abs_cast]
  ext τ
  simp [Complex.real_smul]
