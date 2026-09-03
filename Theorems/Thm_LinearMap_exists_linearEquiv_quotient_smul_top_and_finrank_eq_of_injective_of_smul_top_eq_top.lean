import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_exists_linearEquiv_quotient_smul_top_and_finrank_eq_of_injective_of_smul_top_eq_top

set_option autoImplicit false

theorem LinearMap.exists_linearEquiv_quotient_smul_top_and_finrank_eq_of_injective_of_smul_top_eq_top
    {R : Type*} [CommRing R] (𝔪 : Ideal R)
    {Y L : Type*} [AddCommGroup Y] [Module R Y] [AddCommGroup L] [Module R L]
    (f : Y →ₗ[R] L) (hf : Function.Injective f)
    [Module.Finite R (L ⧸ LinearMap.range f)]
    (hC : (𝔪 • ⊤ : Submodule R (L ⧸ LinearMap.range f)) = ⊤) :
    (∃ e : (Y ⧸ (𝔪 • ⊤ : Submodule R Y)) ≃ₗ[R] (L ⧸ (𝔪 • ⊤ : Submodule R L)),
        ∀ y : Y, e (Submodule.Quotient.mk y) = Submodule.Quotient.mk (f y)) ∧
    Module.finrank (R ⧸ 𝔪) (Y ⧸ (𝔪 • ⊤ : Submodule R Y)) = Module.finrank (R ⧸ 𝔪) (L ⧸ (𝔪 • ⊤ : Submodule R L)) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_linearEquiv_quotient_smul_top_and_finrank_eq_of_injective_of_smul_top_eq_top.solution
