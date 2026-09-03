import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_unit_pow_of_torsor_grading_nsmul

set_option autoImplicit false

theorem HopfAlgebra.exists_unit_pow_of_torsor_grading_nsmul
    {Λ : Type} [AddCommGroup Λ]
    {R T : Type} [CommRing R] [CommRing T] [Algebra R T]
    (hinj : Function.Injective (algebraMap R T))
    (L : Λ → Submodule R T)
    (hL0 : L 0 = Submodule.span R {(1 : T)})
    (hcyc : ∀ j, ∃ t : T, L j = Submodule.span R {t})
    (hmul : ∀ i j, ∀ x ∈ L i, ∀ y ∈ L j, x * y ∈ L (i + j))
    (htorsor : ∀ i j, L (i + j) ≤ Submodule.span R {z | ∃ x ∈ L i, ∃ y ∈ L j, z = x * y})
    (g : Λ) (Q : ℕ) (hgQ : Q • g = 0) :
    ∃ (t : T) (u : R), IsUnit u ∧ L g = Submodule.span R {t} ∧
      t ^ Q = algebraMap R T u ∧
      ∀ j : ℕ, L (j • g) = Submodule.span R {t ^ j} := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_unit_pow_of_torsor_grading_nsmul.solution
