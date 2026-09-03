import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_AtkinLehnerDatum
import P2M.Util
import P2M.Sol.S_ModularForm_mdifferentiable_add_heckeU_alSlash

theorem ModularForm.mdifferentiable_add_heckeU_alSlash {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (f + ModularForm.heckeU k q (ModularForm.alSlash W k f)) := by p2m_exact_reverting @_root_.P2MW.S_ModularForm_mdifferentiable_add_heckeU_alSlash.solution
