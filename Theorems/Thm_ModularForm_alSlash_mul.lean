import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
import P2M.Sol.S_ModularForm_alSlash_mul

open UpperHalfPlane
theorem ModularForm.alSlash_mul {M q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M q) (k₁ k₂ : ℤ) (F G : ℍ → ℂ) : ModularForm.alSlash W (k₁ + k₂) (F * G) = (q : ℂ) • (ModularForm.alSlash W k₁ F * ModularForm.alSlash W k₂ G) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_alSlash_mul.solution
