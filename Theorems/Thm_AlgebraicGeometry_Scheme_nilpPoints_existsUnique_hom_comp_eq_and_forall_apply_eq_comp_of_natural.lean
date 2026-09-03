import Mathlib
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_hom_comp_eq_and_forall_apply_eq_comp_of_natural

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.nilpPoints.existsUnique_hom_comp_eq_and_forall_apply_eq_comp_of_natural
    {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪]
    {X Y : Scheme.{0}} (fX : X ⟶ Spec (.of 𝒪)) (fY : Y ⟶ Spec (.of 𝒪)) [LocallyOfFiniteType fX]
    (τ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [IsNoetherianRing B],
      (Scheme.nilpPoints fX).obj B → (Scheme.nilpPoints fY).obj B)
    (hτ : ∀ (B B' : Type) [CommRing B] [Algebra 𝒪 B] [IsNoetherianRing B] [CommRing B'] [Algebra 𝒪 B'] [IsNoetherianRing B']
      (g : B →ₐ[𝒪] B') (φ : (Scheme.nilpPoints fX).obj B),
      τ B' ((Scheme.nilpPoints fX).map g φ) = (Scheme.nilpPoints fY).map g (τ B φ)) :
    ∃! h : X ⟶ Y, h ≫ fY = fX ∧
      ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [IsNoetherianRing B] (φ : (Scheme.nilpPoints fX).obj B),
        (τ B φ).1 = φ.1 ≫ h := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_hom_comp_eq_and_forall_apply_eq_comp_of_natural.solution
