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
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_frobenius_eq_verschiebungInt_of_hasStructureConstants_of_apply_zero_eq_zero

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule in

theorem CerednikDrinfeld.FormalODModule.exists_frobenius_eq_verschiebungInt_of_hasStructureConstants_of_apply_zero_eq_zero
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    (X₀ : FormalODModule q k)
    (hV : Function.Injective (MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := X₀.F)))
    (γ : Fin 2 → MvFormalGroup.CartierModule q X₀.F) (a : ℕ → Fin 2 → k) (ha : X₀.HasStructureConstants γ a)
    (i₀ : Fin 2) (h0 : a 0 i₀ = 0) :
    ∃ y : MvFormalGroup.CartierModule q X₀.F,
      MvFormalGroup.CartierModule.frobenius (γ i₀) = MvFormalGroup.CartierModule.verschiebungInt y := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_frobenius_eq_verschiebungInt_of_hasStructureConstants_of_apply_zero_eq_zero.solution
