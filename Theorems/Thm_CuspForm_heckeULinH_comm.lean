import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import P2M.Util
import P2M.Sol.S_CuspForm_heckeULinH_comm
attribute [-instance] WeierstrassCurve.Affine.Point.instFinite

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.heckeULinH_comm
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)
    {q q' : ℕ} (hq : q.Prime) (hqM : q ∣ M) (hq' : q'.Prime) (hq'M : q' ∣ M)
    (f : CuspForm (CohCarrier.GammaH M H) k) :
    CuspForm.heckeULinH k q (CuspForm.heckeULinH k q' f) = CuspForm.heckeULinH k q' (CuspForm.heckeULinH k q f) := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_heckeULinH_comm.solution
