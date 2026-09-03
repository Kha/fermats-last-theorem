import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_nonempty_basis_quotient_span_range_map_of_comp_eq_X_pow
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

open MvPowerSeries

universe u

theorem MvFormalGroup.CartierModule.nonempty_basis_quotient_span_range_map_of_comp_eq_X_pow
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p] {d : ℕ}
    (Ψ Ψ' : MvFormalGroup d k) [Ψ.IsComm] [Ψ'.IsComm] (π : Ψ.Hom Ψ')
    (ρ : Ψ'.Hom (Ψ.map (_root_.frobenius k p)))
    (hcomp : ∀ i, (ρ.comp π).toPowerSeries i = (X i : MvPowerSeries (Fin d) k) ^ p)
    (hfin : Module.Finite k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ρ.toPowerSeries))) :
    Nonempty (Module.Basis (Fin (MvFormalGroup.linearPart ρ.toPowerSeries).rank)
      (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
      ((MvFormalGroup.CartierModule p Ψ' ⧸
          (Ideal.span {(p : WittVector p k)} • ⊤ :
            Submodule (WittVector p k) (MvFormalGroup.CartierModule p Ψ'))) ⧸
        Submodule.span (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
          (Set.range fun g : MvFormalGroup.CartierModule p Ψ =>
            (Submodule.Quotient.mk (MvFormalGroup.CartierModule.map π g) :
              MvFormalGroup.CartierModule p Ψ' ⧸
                (Ideal.span {(p : WittVector p k)} • ⊤ :
                  Submodule (WittVector p k) (MvFormalGroup.CartierModule p Ψ')))))) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_nonempty_basis_quotient_span_range_map_of_comp_eq_X_pow.solution
