import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_isLocalization_away_pullbackRing_of_comp_eq

set_option autoImplicit false
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.isLocalization_away_pullbackRing_of_comp_eq
    {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) (g : ModuliPackage.pullbackRing φ' φ'')
    (B₁ B'₁ B''₁ : Type) [CommRing B₁] [CommRing B'₁] [CommRing B''₁]
    [Algebra B B₁] [Algebra B' B'₁] [Algebra B'' B''₁]
    [IsLocalization.Away (φ' g.1.1) B₁] [IsLocalization.Away g.1.1 B'₁] [IsLocalization.Away g.1.2 B''₁]
    (φ'₁ : B'₁ →+* B₁) (φ''₁ : B''₁ →+* B₁)
    (hφ'₁ : φ'₁.comp (algebraMap B' B'₁) = (algebraMap B B₁).comp φ')
    (hφ''₁ : φ''₁.comp (algebraMap B'' B''₁) = (algebraMap B B₁).comp φ'')
    (δ : ModuliPackage.pullbackRing φ' φ'' →+* ModuliPackage.pullbackRing φ'₁ φ''₁)
    (hδ₁ : (ModuliPackage.pullbackFst φ'₁ φ''₁).comp δ =
      (algebraMap B' B'₁).comp (ModuliPackage.pullbackFst φ' φ''))
    (hδ₂ : (ModuliPackage.pullbackSnd φ'₁ φ''₁).comp δ =
      (algebraMap B'' B''₁).comp (ModuliPackage.pullbackSnd φ' φ'')) :
    @IsLocalization.Away (ModuliPackage.pullbackRing φ' φ'') _ g (ModuliPackage.pullbackRing φ'₁ φ''₁) _
      δ.toAlgebra ∧
    (Function.Surjective φ' → Function.Surjective φ'₁) ∧
    (Function.Surjective φ'' → Function.Surjective φ''₁) ∧
    (IsNilpotent (RingHom.ker φ') → IsNilpotent (RingHom.ker φ'₁)) ∧
    (IsNilpotent (RingHom.ker φ'') → IsNilpotent (RingHom.ker φ''₁)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_isLocalization_away_pullbackRing_of_comp_eq.solution
