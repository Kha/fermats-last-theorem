import Definitions.Def_ModularCurve_TwoNewEigenformIdeal
import Definitions.Def_ModularCurve_EigenformIdeal
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_mTorsionNeBot_of_isTwoNewEigenformIdeal
set_option autoImplicit false
open ModularCurve

theorem CerednikDrinfeld.mTorsionNeBot_of_isTwoNewEigenformIdeal {M q q' : ℕ} (p : ℕ)
    (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
    (hES : EigenformSupportAt M p J) {𝔪 : Ideal HeckeAlg}
    (h𝔪 : IsTwoNewEigenformIdeal M q q' 𝔪) (hp : (p : HeckeAlg) ∈ 𝔪) :
    MTorsionNeBot HeckeAlg J 𝔪 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_mTorsionNeBot_of_isTwoNewEigenformIdeal.solution
