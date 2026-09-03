import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_algebraMap_norm_eq_prod_apply_of_card_eq_finrank

set_option autoImplicit false

universe u v w

theorem Algebra.algebraMap_norm_eq_prod_apply_of_card_eq_finrank
    {W : Type u} [CommRing W] {T : Type v} [CommRing T] [Algebra W T] [Module.Free W T] [Module.Finite W T]
    {L : Type w} [Field L] [Algebra W L]
    {ι : Type*} [Fintype ι] (σ : ι → (T →ₐ[W] L)) (hσ : Function.Injective σ)
    (hcard : Fintype.card ι = Module.finrank W T) (a : T) :
    algebraMap W L (Algebra.norm W a) = ∏ i, σ i a := by p2m_exact_reverting @_root_.P2MW.S_Algebra_algebraMap_norm_eq_prod_apply_of_card_eq_finrank.solution
