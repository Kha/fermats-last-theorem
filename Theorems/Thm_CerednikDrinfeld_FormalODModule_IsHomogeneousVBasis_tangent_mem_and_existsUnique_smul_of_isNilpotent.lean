import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_IsHomogeneousVBasis_tangent_mem_and_existsUnique_smul_of_isNilpotent

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.IsHomogeneousVBasis.tangent_mem_and_existsUnique_smul_of_isNilpotent
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B) (hB : IsNilpotent (p : B))
    (X : CerednikDrinfeld.FormalODModule p B)
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ) :
    (MvFormalGroup.CartierModule.tangent (γ 0) ∈ X.lieZero j ∧
      MvFormalGroup.CartierModule.tangent (γ 1) ∈ X.lieOne j) ∧
    (∀ v ∈ X.lieZero j, ∃! b : B, v = b • MvFormalGroup.CartierModule.tangent (γ 0)) ∧
    (∀ v ∈ X.lieOne j, ∃! b : B, v = b • MvFormalGroup.CartierModule.tangent (γ 1)) ∧
    IsCompl (X.lieZero j) (X.lieOne j) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_IsHomogeneousVBasis_tangent_mem_and_existsUnique_smul_of_isNilpotent.solution
