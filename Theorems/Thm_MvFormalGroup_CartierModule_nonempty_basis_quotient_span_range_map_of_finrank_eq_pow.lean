import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import P2M.Util
import P2M.Sol.S_MvFormalGroup_CartierModule_nonempty_basis_quotient_span_range_map_of_finrank_eq_pow
attribute [-instance] instTopologicallyFGOfFiniteType
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

open MvPowerSeries

universe u

theorem MvFormalGroup.CartierModule.nonempty_basis_quotient_span_range_map_of_finrank_eq_pow
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] [PerfectRing k p] {d : ℕ}
    (Ψ Φ : MvFormalGroup d k) [Ψ.IsComm] [Φ.IsComm] (ψ : Ψ.Hom Φ) (e : ℕ)
    (hdeg : Module.finrank k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) = p ^ e)
    (hp : ∀ f : MvFormalGroup.CartierModule p Φ, ∃ g : MvFormalGroup.CartierModule p Ψ,
      MvFormalGroup.CartierModule.map ψ g = (p : WittVector p k) • f) :
    Nonempty (Module.Basis (Fin e) (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
      ((MvFormalGroup.CartierModule p Φ ⧸
          (Ideal.span {(p : WittVector p k)} • ⊤ :
            Submodule (WittVector p k) (MvFormalGroup.CartierModule p Φ))) ⧸
        Submodule.span (WittVector p k ⧸ Ideal.span {(p : WittVector p k)})
          (Set.range fun g : MvFormalGroup.CartierModule p Ψ =>
            (Submodule.Quotient.mk (MvFormalGroup.CartierModule.map ψ g) :
              MvFormalGroup.CartierModule p Φ ⧸
                (Ideal.span {(p : WittVector p k)} • ⊤ :
                  Submodule (WittVector p k) (MvFormalGroup.CartierModule p Φ)))))) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_nonempty_basis_quotient_span_range_map_of_finrank_eq_pow.solution
