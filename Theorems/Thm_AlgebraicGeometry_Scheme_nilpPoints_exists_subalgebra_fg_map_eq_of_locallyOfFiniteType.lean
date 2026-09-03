import Mathlib
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_nilpPoints_exists_subalgebra_fg_map_eq_of_locallyOfFiniteType

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.FormalOmega

theorem AlgebraicGeometry.Scheme.nilpPoints.exists_subalgebra_fg_map_eq_of_locallyOfFiniteType
    {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪]
    (R : Type) [CommRing R] [Algebra 𝒪 R]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of 𝒪)) [LocallyOfFiniteType f] :
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra R B] [IsScalarTower 𝒪 R B] (y : (Scheme.nilpPoints f).obj B),
        ∃ (S : Subalgebra R B) (_ : S.FG) (y₀ : (Scheme.nilpPoints f).obj ↥S),
          (Scheme.nilpPoints f).map ((S.val).restrictScalars 𝒪) y₀ = y) ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra R B] [IsScalarTower 𝒪 R B]
        (S₁ S₂ : Subalgebra R B), S₁.FG → S₂.FG →
        ∀ (y₁ : (Scheme.nilpPoints f).obj ↥S₁) (y₂ : (Scheme.nilpPoints f).obj ↥S₂),
        (Scheme.nilpPoints f).map ((S₁.val).restrictScalars 𝒪) y₁ = (Scheme.nilpPoints f).map ((S₂.val).restrictScalars 𝒪) y₂ →
        ∃ (S₃ : Subalgebra R B) (_ : S₃.FG) (h₁ : S₁ ≤ S₃) (h₂ : S₂ ≤ S₃),
          (Scheme.nilpPoints f).map ((Subalgebra.inclusion h₁).restrictScalars 𝒪) y₁ =
            (Scheme.nilpPoints f).map ((Subalgebra.inclusion h₂).restrictScalars 𝒪) y₂) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_nilpPoints_exists_subalgebra_fg_map_eq_of_locallyOfFiniteType.solution
