import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_GradedCartierModuleData_length_piece_quotient_eq_of_isHomogeneousVBasis_of_comm_verschiebung

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.GradedCartierModuleData.length_piece_quotient_eq_of_isHomogeneousVBasis_of_comm_verschiebung
    (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [CharP K p] [PerfectRing K p] {j : Zp2 p →+* K}
    (D D' : GradedCartierModuleData p K j)
    (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ)
    (γ' : Fin 2 → D'.M) (hγ' : D'.IsHomogeneousVBasis γ')
    (f : D.M →ₗ[WittVector p K] D'.M) (hf : Function.Injective f)
    (hfV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hfdeg : ∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i) :
    Module.length (WittVector p K)
        (↥(D'.piece 0) ⧸ Submodule.comap (D'.piece 0).subtype (Submodule.map f (D.piece 0))) =
      Module.length (WittVector p K)
        (↥(D'.piece 1) ⧸ Submodule.comap (D'.piece 1).subtype (Submodule.map f (D.piece 1))) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_length_piece_quotient_eq_of_isHomogeneousVBasis_of_comm_verschiebung.solution
