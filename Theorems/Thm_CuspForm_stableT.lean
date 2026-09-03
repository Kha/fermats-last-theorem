import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import P2M.Util
import P2M.Sol.S_CuspForm_stableT
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite

set_option autoImplicit false

p2m_open "scoped MatrixGroups ModularForm~mdifferentiable_heckeU~heckeU_add_slash_slash_eq_self_of_mem_GammaH"

theorem CuspForm.stableT (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    CuspForm.StableT M H k ℓ := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_stableT.solution
