import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_isGalois_functionField_of_quotient_of_finite

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_isGalois_functionField_of_quotient_of_finite
    {B : Type} [CommRing B]
    {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X]
    (πC : C ⟶ Spec (CommRingCat.of B)) [IsSeparated πC]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut C) (hρ : ∀ g : G, (ρ g).hom ≫ πC = πC)
    (π : C ⟶ X) [IsFinite π] (hπ : ∀ g : G, (ρ g).hom ≫ π = π)
    (hsurj : Function.Surjective π.base)
    (hsec : ∀ V : X.Opens, Function.Injective (π.app V))
    (hinv : ∀ V : X.Opens, Set.range (π.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (π ⁻¹ᵁ V) (π ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hπ g]) s = s}) :
    ∃ (_ : Algebra X.functionField C.functionField)
      (θ : G →* (C.functionField ≃ₐ[X.functionField] C.functionField)),

      (∀ (V : X.Opens) [Nonempty (V : Scheme.{0})] [Nonempty ((π ⁻¹ᵁ V : C.Opens) : Scheme.{0})] (f : Γ(X, V)),
        algebraMap X.functionField C.functionField (X.germToFunctionField V f) =
          C.germToFunctionField (π ⁻¹ᵁ V) (π.app V f)) ∧

      (∀ (g : G) (U : C.Opens) [Nonempty (U : Scheme.{0})] [Nonempty (((ρ g).inv ⁻¹ᵁ U : C.Opens) : Scheme.{0})] (f : Γ(C, U)),
        θ g (C.germToFunctionField U f) = C.germToFunctionField ((ρ g).inv ⁻¹ᵁ U) ((ρ g).inv.app U f)) ∧
      FiniteDimensional X.functionField C.functionField ∧ IsGalois X.functionField C.functionField ∧
      Function.Surjective θ ∧ (∀ g : G, θ g = 1 ↔ ρ g = 1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isGalois_functionField_of_quotient_of_finite.solution
