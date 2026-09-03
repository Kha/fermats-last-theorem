import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_surjective
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_eq_zero_iff_exists_verschiebung_eq
import P2M.Util
namespace P2MW.S_MvFormalGroup_CartierModule_tangent_surjective_and_tangent_eq_zero_iff_exists_verschiebung_eq
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u

theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] [CharP R p] {d : ℕ}
    (Φ : MvFormalGroup d R) [Φ.IsComm] :
    Function.Surjective
        (MvFormalGroup.CartierModule.tangent :
          MvFormalGroup.CartierModule p Φ → Fin d → R) ∧
      ∀ f : MvFormalGroup.CartierModule p Φ,
        MvFormalGroup.CartierModule.tangent f = 0 ↔
          ∃ g : MvFormalGroup.CartierModule p Φ,
            MvFormalGroup.CartierModule.verschiebung g = f :=
  ⟨MvFormalGroup.CartierModule.tangent_surjective p Φ,
    MvFormalGroup.CartierModule.tangent_eq_zero_iff_exists_verschiebung_eq p Φ⟩
