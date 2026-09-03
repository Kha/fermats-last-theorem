import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_of_forall_pullbackSection_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.eq_of_forall_pullbackSection_eq
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [IsReduced X]
    {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) (σ₁ σ₂ : 𝟙_ X.Modules ⟶ L)
    (h : ∀ p : Spec (CommRingCat.of k) ⟶ X, p ≫ f = 𝟙 _ →
      Scheme.Modules.pullbackSection p σ₁ = Scheme.Modules.pullbackSection p σ₂) :
    σ₁ = σ₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_of_forall_pullbackSection_eq.solution
