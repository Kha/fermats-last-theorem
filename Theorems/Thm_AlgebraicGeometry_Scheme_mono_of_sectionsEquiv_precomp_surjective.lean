import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_mono_of_sectionsEquiv_precomp_surjective

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

theorem AlgebraicGeometry.Scheme.mono_of_sectionsEquiv_precomp_surjective
    (F F' : Sheaf (smallFppfTopology specInt) Ab.{1})
    (H H' : Type) [CommRing H] [CommRing H'] [HopfAlgebra ℤ H] [HopfAlgebra ℤ H']
    (eF : ∀ U : specInt.Fppf, F.1.obj (op U) ≃+ Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤))))
    (eF' : ∀ U : specInt.Fppf, F'.1.obj (op U) ≃+ Additive (WithConv (H' →ₐ[ℤ] Γ(U.left, ⊤))))
    (π : H' →ₐ[ℤ] H) (hπ : Function.Surjective π)
    (incl : F ⟶ F')
    (hincl : ∀ (U : specInt.Fppf) (s : F.1.obj (op U)) (h' : H'),
      (Additive.toMul (eF' U (incl.1.app (op U) s))) h' = (Additive.toMul (eF U s)) (π h')) :
    Mono incl := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_mono_of_sectionsEquiv_precomp_surjective.solution
