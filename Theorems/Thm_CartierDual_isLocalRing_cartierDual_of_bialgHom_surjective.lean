import Mathlib
import Definitions.Def_HopfAlgebra_CartierDualInstances
import P2M.Util
import P2M.Sol.S_CartierDual_isLocalRing_cartierDual_of_bialgHom_surjective

set_option autoImplicit false

theorem CartierDual.isLocalRing_cartierDual_of_bialgHom_surjective
    (R : Type) [CommRing R]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H]
    (HV : Type) [CommRing HV] [HopfAlgebra R HV] [Module.Finite R HV] [Module.Free R HV]
    [Coalgebra.IsCocomm R HV] [Nontrivial HV]
    (π : H →ₐc[R] HV) (hπ : Function.Surjective π)
    (hdual : IsLocalRing (CartierDual R H)) :
    IsLocalRing (CartierDual R HV) := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_isLocalRing_cartierDual_of_bialgHom_surjective.solution
