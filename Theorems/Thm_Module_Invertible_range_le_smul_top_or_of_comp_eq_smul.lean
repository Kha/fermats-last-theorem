import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Invertible_range_le_smul_top_or_of_comp_eq_smul

set_option autoImplicit false

theorem Module.Invertible.range_le_smul_top_or_of_comp_eq_smul
    {R : Type*} [CommRing R] {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [Module.Invertible R P] [Module.Invertible R Q] (f : P →ₗ[R] Q) (g : Q →ₗ[R] P) (a : R)
    (hfg : g ∘ₗ f = a • LinearMap.id) (x : PrimeSpectrum R) (ha : a ∈ x.asIdeal) :
    LinearMap.range f ≤ x.asIdeal • (⊤ : Submodule R Q) ∨ LinearMap.range g ≤ x.asIdeal • (⊤ : Submodule R P) := by p2m_exact_reverting @_root_.P2MW.S_Module_Invertible_range_le_smul_top_or_of_comp_eq_smul.solution
