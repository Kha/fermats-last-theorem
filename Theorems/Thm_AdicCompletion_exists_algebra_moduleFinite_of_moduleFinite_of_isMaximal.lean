import Mathlib
import P2M.Util
import P2M.Sol.S_AdicCompletion_exists_algebra_moduleFinite_of_moduleFinite_of_isMaximal
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal
attribute [-simp] AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.map_smul_of AdicCompletion.algebraMap_of AdicCompletion.stabilizer_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul

set_option autoImplicit false

open IsLocalRing

theorem AdicCompletion.exists_algebra_moduleFinite_of_moduleFinite_of_isMaximal
    (B C : Type) [CommRing B] [IsNoetherianRing B] [CommRing C] [Algebra B C] [Module.Finite B C]
    (𝔫 : Ideal C) [𝔫.IsMaximal] :
    ∃ (_ : Algebra (AdicCompletion (𝔫.comap (algebraMap B C)) B) (AdicCompletion 𝔫 C))
      (_ : IsScalarTower B (AdicCompletion (𝔫.comap (algebraMap B C)) B) (AdicCompletion 𝔫 C)),
      Module.Finite (AdicCompletion (𝔫.comap (algebraMap B C)) B) (AdicCompletion 𝔫 C) ∧
      (Module.Flat B C →
        Function.Injective (algebraMap (AdicCompletion (𝔫.comap (algebraMap B C)) B) (AdicCompletion 𝔫 C))) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_exists_algebra_moduleFinite_of_moduleFinite_of_isMaximal.solution
