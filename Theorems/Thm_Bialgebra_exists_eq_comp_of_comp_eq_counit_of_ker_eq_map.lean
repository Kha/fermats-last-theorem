import Mathlib
import P2M.Util
import P2M.Sol.S_Bialgebra_exists_eq_comp_of_comp_eq_counit_of_ker_eq_map

set_option autoImplicit false

open scoped TensorProduct

universe u v w x

theorem Bialgebra.exists_eq_comp_of_comp_eq_counit_of_ker_eq_map
    {R : Type u} [CommRing R]
    {B : Type v} [CommRing B] [Bialgebra R B]
    {G₁ : Type w} [CommRing G₁] [Bialgebra R G₁]
    {G₂ : Type x} [CommRing G₂] [Bialgebra R G₂]
    (π : B →ₐc[R] G₁) (hπ : Function.Surjective π)
    (j : G₂ →ₐc[R] B)
    (hex : RingHom.ker (π : B →ₐ[R] G₁) =
      Ideal.map (j : G₂ →ₐ[R] B) (RingHom.ker (Bialgebra.counitAlgHom R G₂)))
    (x : B →ₐc[R] B)
    (hx : (x : B →ₐ[R] B).comp (j : G₂ →ₐ[R] B) = (Algebra.ofId R B).comp (Bialgebra.counitAlgHom R G₂)) :
    ∃ y : G₁ →ₐc[R] B, x = y.comp π := by p2m_exact_reverting @_root_.P2MW.S_Bialgebra_exists_eq_comp_of_comp_eq_counit_of_ker_eq_map.solution
