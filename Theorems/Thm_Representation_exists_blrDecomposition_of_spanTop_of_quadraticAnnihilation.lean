import Mathlib
import P2M.Util
import P2M.Sol.S_Representation_exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation
set_option autoImplicit false
open Matrix

theorem Representation.exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation
    {k : Type} [Field k] {G : Type} [Group G]
    (ρ : G →* Matrix (Fin 2) (Fin 2) k)
    {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (σW : Representation k G W)
    (h2 : (2 : k) ≠ 0)
    (hirr : Submodule.span k (Set.range (fun g : G => ρ g)) = ⊤)
    (hann : ∀ g : G,
      σW g ^ 2 - Matrix.trace (ρ g) • σW g + (ρ g).det • (1 : W →ₗ[k] W) = 0) :
    ∃ (n : ℕ) (e : W ≃ₗ[k] (Fin n → (Fin 2 → k))),
      ∀ (g : G) (w : W) (i : Fin n), e (σW g w) i = (ρ g).mulVec (e w i) := by p2m_exact_reverting @_root_.P2MW.S_Representation_exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation.solution
