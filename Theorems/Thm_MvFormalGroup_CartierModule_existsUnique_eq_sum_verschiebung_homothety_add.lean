import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebung_homothety_add

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.existsUnique_eq_sum_verschiebung_homothety_add
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm]
    (f : Fin d → MvFormalGroup.CartierModule p Φ)
    (hf : IsUnit (Matrix.of fun i j => MvFormalGroup.CartierModule.tangent (f i) j).det)
    (g : MvFormalGroup.CartierModule p Φ) (N : ℕ) :
    ∃! ch : (Fin N → Fin d → R) × MvFormalGroup.CartierModule p Φ,
      g = (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := Φ)))^[m]
              (∑ i : Fin d, MvFormalGroup.CartierModule.homothety (ch.1 m i) (f i))) +
          (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := Φ)))^[N] ch.2 := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebung_homothety_add.solution
