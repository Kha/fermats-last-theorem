import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_endAct_varpiEnd_eq_verschiebung_of_isAlgClosed
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_endAct_varpiEnd_eq_verschiebung_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (Φ : CerednikDrinfeld.SpecialFormalODModule p j) :
    ∃ e : Fin 2 → MvFormalGroup.CartierModule p Φ.F,
      (∀ r, e r ∈ Φ.gradedPiece j 0) ∧
      (∀ r, MvFormalGroup.CartierModule.endAct Φ.varpiEnd (e r) =
        MvFormalGroup.CartierModule.verschiebung (e r)) ∧
      (∀ w : Fin 2 → WittVector p k, ∑ r, w r • e r = 0 → w = 0) ∧
      (∀ f ∈ Φ.gradedPiece j 0, ∃ w : Fin 2 → WittVector p k,
        (p : WittVector p k) • f = ∑ r, w r • e r) ∧
      (∀ f ∈ Φ.gradedPiece j 1, ∃ w : Fin 2 → WittVector p k,
        MvFormalGroup.CartierModule.endAct Φ.varpiEnd f = ∑ r, w r • e r) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_endAct_varpiEnd_eq_verschiebung_of_isAlgClosed.solution
