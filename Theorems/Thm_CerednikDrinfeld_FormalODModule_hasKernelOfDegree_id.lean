import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_id

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.hasKernelOfDegree_id
    (B : Type) [CommRing B] :
    FormalODModule.HasKernelOfDegree (Series.id B) 1 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_id.solution
