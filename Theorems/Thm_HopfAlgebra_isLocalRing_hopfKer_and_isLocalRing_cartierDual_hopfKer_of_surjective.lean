import Mathlib
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_HopfAlgebra_HopfKerHopf
import P2M.Util
import P2M.Sol.S_HopfAlgebra_isLocalRing_hopfKer_and_isLocalRing_cartierDual_hopfKer_of_surjective

set_option autoImplicit false

theorem HopfAlgebra.isLocalRing_hopfKer_and_isLocalRing_cartierDual_hopfKer_of_surjective
    (R : Type) [CommRing R]
    (H : Type) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H] [Coalgebra.IsCocomm R H]
    (HV : Type) [CommRing HV] [HopfAlgebra R HV] [Module.Finite R HV] [Module.Free R HV]
    [Coalgebra.IsCocomm R HV] [Nontrivial HV]
    (π : H →ₐc[R] HV) (hπ : Function.Surjective π)
    [Module.Finite R ↥(HopfAlgebra.hopfKer π)] [Module.Free R ↥(HopfAlgebra.hopfKer π)]
    (hloc : IsLocalRing H) (hdual : IsLocalRing (CartierDual R H)) :
    IsLocalRing ↥(HopfAlgebra.hopfKer π) ∧ IsLocalRing (CartierDual R ↥(HopfAlgebra.hopfKer π)) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_isLocalRing_hopfKer_and_isLocalRing_cartierDual_hopfKer_of_surjective.solution
