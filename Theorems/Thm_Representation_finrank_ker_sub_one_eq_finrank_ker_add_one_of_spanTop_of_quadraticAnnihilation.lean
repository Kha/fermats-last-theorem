import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_finrank_ker_sub_one_eq_finrank_ker_add_one_of_spanTop_of_quadraticAnnihilation

set_option autoImplicit false

theorem Representation.finrank_ker_sub_one_eq_finrank_ker_add_one_of_spanTop_of_quadraticAnnihilation
    {k : Type} [Field k] {G : Type} [Group G]
    (ρ : G →* Matrix (Fin 2) (Fin 2) k)
    {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (σW : Representation k G W)
    (h2 : (2 : k) ≠ 0)
    (hirr : Submodule.span k (Set.range (fun g : G => ρ g)) = ⊤)
    (ψ : G →* kˣ)
    (hann : ∀ g : G,
      σW g ^ 2 - Matrix.trace (ρ g) • σW g + ((ψ g : kˣ) : k) • (1 : W →ₗ[k] W) = 0)
    (c : G) (hc : c * c = 1) (hψc : ψ c = -1) :
    Module.finrank k ↥(LinearMap.ker (σW c - 1)) =
      Module.finrank k ↥(LinearMap.ker (σW c + 1)) := by p2m_exact_reverting @_root_.P2MW.S_Representation_finrank_ker_sub_one_eq_finrank_ker_add_one_of_spanTop_of_quadraticAnnihilation.solution
