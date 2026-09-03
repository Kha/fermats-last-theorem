import Mathlib
import Definitions.Def_PDivisibleGroup_Dimension
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_nonempty_basis_cotangentModule_of_hasDimension

set_option autoImplicit false

theorem PDivisibleGroup.nonempty_basis_cotangentModule_of_hasDimension
    {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {p h : ℕ} (hp : (p : R) ∈ I) (G : PDivisibleGroup R p h) {n : ℕ} (hn : G.HasDimension n) :
    Nonempty (Module.Basis (Fin n) R G.cotangentModule) ∧
      (∀ v, Function.Surjective (G.cotangentModuleProj v)) ∧
      ∀ v, LinearMap.ker (G.cotangentModuleProj v) =
        Ideal.span {(p : R) ^ v} • (⊤ : Submodule R G.cotangentModule) := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_nonempty_basis_cotangentModule_of_hasDimension.solution
