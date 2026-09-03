import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_hom_eq_of_forall_map_apply_eq_of_isHomogeneousVBasis
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule

theorem CerednikDrinfeld.FormalODModule.hom_eq_of_forall_map_apply_eq_of_isHomogeneousVBasis
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] (j : CerednikDrinfeld.Zp2 p →+* B)
    (X : CerednikDrinfeld.FormalODModule p B) {d' : ℕ} (G : MvFormalGroup d' B) [G.IsComm]
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (φ ψ : MvFormalGroup.Hom X.F G)
    (h : ∀ i : Fin 2, MvFormalGroup.CartierModule.map φ (γ i) = MvFormalGroup.CartierModule.map ψ (γ i)) :
    φ = ψ := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_hom_eq_of_forall_map_apply_eq_of_isHomogeneousVBasis.solution
