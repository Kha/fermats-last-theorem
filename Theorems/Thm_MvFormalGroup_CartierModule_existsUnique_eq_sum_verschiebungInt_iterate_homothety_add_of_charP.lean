import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebungInt_iterate_homothety_add_of_charP

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.existsUnique_eq_sum_verschiebungInt_iterate_homothety_add_of_charP
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p]
    {d : ℕ} (Φ : MvFormalGroup d R) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (hf : IsUnit (Matrix.of fun i j => MvFormalGroup.CartierModule.tangent (f i) j).det)
    (g : MvFormalGroup.CartierModule p Φ) (N : ℕ) :
    ∃! ch : (Fin N → Fin d → R) × MvFormalGroup.CartierModule p Φ,
      g = (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)]
              (∑ i : Fin d, MvFormalGroup.CartierModule.homothety (ch.1 m i) (f i))) +
          (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] ch.2 := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebungInt_iterate_homothety_add_of_charP.solution
