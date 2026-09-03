import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_map_pullbackFst_eq_and_isIso_map_pullbackSnd_of_isIso

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.exists_map_pullbackFst_eq_and_isIso_map_pullbackSnd_of_isIso
    (p : ℕ) [Fact p.Prime] {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hs'' : Function.Surjective φ'') (hn'' : IsNilpotent (RingHom.ker φ''))
    (X' : FormalODModule p B') (X'' : FormalODModule p B'')
    (w : (X'.map φ').Hom (X''.map φ'')) (hw : w.IsIso) :
    ∃ (X : FormalODModule p (ModuliPackage.pullbackRing φ' φ''))
      (Ψ : (X.map (ModuliPackage.pullbackSnd φ' φ'')).Hom X''),
      X.map (ModuliPackage.pullbackFst φ' φ'') = X' ∧ Ψ.IsIso ∧ Ψ.toSeries.map φ'' = w.toSeries := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_map_pullbackFst_eq_and_isIso_map_pullbackSnd_of_isIso.solution
