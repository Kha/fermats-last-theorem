import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_ker_pullback_fst_specMap_eq_bot_of_field

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.ker_pullback_fst_specMap_eq_bot_of_field
    {k₀ : Type} [Field k₀] {Bb : Type} [CommRing Bb] [Nontrivial Bb] (ψ : k₀ →+* Bb)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) :
    (pullback.fst t (Spec.map (CommRingCat.ofHom ψ))).ker = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_ker_pullback_fst_specMap_eq_bot_of_field.solution
