import Mathlib
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_isCompl_nPiece_zero_one

set_option autoImplicit false

theorem CerednikDrinfeld.GradedCartierModuleData.isCompl_nPiece_zero_one
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) :
    IsCompl (D.nPiece 0) (D.nPiece 1) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_isCompl_nPiece_zero_one.solution
