import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import P2M.Util
import P2M.Sol.S_CuspForm_stableU
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite

set_option autoImplicit false

p2m_open "scoped MatrixGroups ModularForm~mdifferentiable_heckeU~heckeU_slash_eq_self_of_mem_GammaH"

theorem CuspForm.stableU (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) {q : ℕ}
    (hq : q.Prime) (hqM : q ∣ M) :
    CuspForm.StableU M H k q := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_stableU.solution
