import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_isNoetherianRing_pullbackRing_of_surjective

set_option autoImplicit false
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.isNoetherianRing_pullbackRing_of_surjective
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    [IsNoetherianRing B'] [IsNoetherianRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : Function.Surjective φ') (hφ'' : Function.Surjective φ'') :
    IsNoetherianRing (ModuliPackage.pullbackRing φ' φ'') := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_isNoetherianRing_pullbackRing_of_surjective.solution
