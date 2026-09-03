import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_tangent_eq_zero_iff_exists_verschiebung_eq

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.tangent_eq_zero_iff_exists_verschiebung_eq
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] (f : MvFormalGroup.CartierModule p Φ) :
    MvFormalGroup.CartierModule.tangent f = 0 ↔
      ∃ g : MvFormalGroup.CartierModule p Φ,
        MvFormalGroup.CartierModule.verschiebung g = f := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_tangent_eq_zero_iff_exists_verschiebung_eq.solution
