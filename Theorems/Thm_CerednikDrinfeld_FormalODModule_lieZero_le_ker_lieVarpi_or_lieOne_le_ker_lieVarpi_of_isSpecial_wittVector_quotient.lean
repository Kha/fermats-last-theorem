import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_lieZero_le_ker_lieVarpi_or_lieOne_le_ker_lieVarpi_of_isSpecial_wittVector_quotient

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.lieZero_le_ker_lieVarpi_or_lieOne_le_ker_lieVarpi_of_isSpecial_wittVector_quotient
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4) :
    Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi ∨
      Φ.lieOne ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_lieZero_le_ker_lieVarpi_or_lieOne_le_ker_lieVarpi_of_isSpecial_wittVector_quotient.solution
