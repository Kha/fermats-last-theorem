import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_pullbackSection_ne_zero_of_finrank_pos

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_pullbackSection_ne_zero_of_finrank_pos
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsReduced X] [LocallyOfFiniteType f]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hpos : letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
      letI : Module k Γ(M, ⊤) := Module.compHom _ (algebraMap k Γ(X, ⊤))
      0 < Module.finrank k Γ(M, ⊤)) :
    ∃ (θ : 𝟙_ X.Modules ⟶ M) (u : Spec (CommRingCat.of k) ⟶ X), u ≫ f = 𝟙 _ ∧
      Scheme.Modules.pullbackSection u θ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_pullbackSection_ne_zero_of_finrank_pos.solution
