import Mathlib
import Definitions.Def_PDivisibleGroup_Dimension
import P2M.Util
import P2M.Sol.S_PDivisibleGroup_ker_cotangentMap_eq_smul_top_and_smul_top_eq_bot

set_option autoImplicit false

theorem PDivisibleGroup.ker_cotangentMap_eq_smul_top_and_smul_top_eq_bot
    {R : Type} [CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h) (v : ℕ) :
    LinearMap.ker (G.cotangentMap v) = Ideal.span {(p : R) ^ v} • ⊤ ∧
      Ideal.span {(p : R) ^ v} • (⊤ : Submodule R (G.Cotangent v)) = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_PDivisibleGroup_ker_cotangentMap_eq_smul_top_and_smul_top_eq_bot.solution
