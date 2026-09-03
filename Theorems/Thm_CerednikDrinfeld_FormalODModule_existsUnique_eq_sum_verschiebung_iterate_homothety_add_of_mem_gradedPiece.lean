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
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_existsUnique_eq_sum_verschiebung_iterate_homothety_add_of_mem_gradedPiece
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.existsUnique_eq_sum_verschiebung_iterate_homothety_add_of_mem_gradedPiece
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] [CharP B p]
    (j : CerednikDrinfeld.Zp2 p →+* B) (X : CerednikDrinfeld.FormalODModule p B)
    (hLie : IsCompl (X.lieZero j) (X.lieOne j))
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (i N : ℕ) (m : MvFormalGroup.CartierModule p X.F) (hm : m ∈ X.gradedPiece j i) :
    ∃! ag : (Fin N → B) × MvFormalGroup.CartierModule p X.F,
      ag.2 ∈ X.gradedPiece j (i + N) ∧
      m = (∑ k : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := X.F)))^[k]
              (MvFormalGroup.CartierModule.homothety (ag.1 k)
                (γ ⟨(i + k) % 2, Nat.mod_lt _ two_pos⟩))) +
          (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := X.F)))^[N] ag.2 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_existsUnique_eq_sum_verschiebung_iterate_homothety_add_of_mem_gradedPiece.solution
