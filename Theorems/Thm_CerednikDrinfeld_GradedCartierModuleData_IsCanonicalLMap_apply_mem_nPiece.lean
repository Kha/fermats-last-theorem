import Mathlib
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_apply_mem_nPiece

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.apply_mem_nPiece
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L) (i : Fin 2) (x : D.M) (hx : x ∈ D.piece i) :
    L x ∈ D.nPiece i := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_apply_mem_nPiece.solution
