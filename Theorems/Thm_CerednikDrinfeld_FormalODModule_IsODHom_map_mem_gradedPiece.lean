import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_IsODHom_map_mem_gradedPiece

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.IsODHom.map_mem_gradedPiece
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (X Y : CerednikDrinfeld.FormalODModule p B) (φ : CerednikDrinfeld.SpecialFormal.Series B)
    (hφ : CerednikDrinfeld.FormalODModule.IsODHom X Y φ) (n : ℕ)
    (m : MvFormalGroup.CartierModule p X.F) (hm : m ∈ X.gradedPiece j n) :
    MvFormalGroup.CartierModule.map hφ.1.toHom m ∈ Y.gradedPiece j n := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_IsODHom_map_mem_gradedPiece.solution
