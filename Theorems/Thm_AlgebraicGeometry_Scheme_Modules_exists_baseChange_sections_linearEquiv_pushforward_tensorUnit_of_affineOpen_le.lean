import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_baseChange_sections_linearEquiv_pushforward_tensorUnit_of_affineOpen_le

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.exists_baseChange_sections_linearEquiv_pushforward_tensorUnit_of_affineOpen_le
    {X Y : Scheme.{u}} (π : Y ⟶ X) [IsAffineHom π]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ U) :
    letI : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map (homOfLE hVU).op).hom.toAlgebra
    ∃ e : Γ(X, V) ⊗[Γ(X, U)] Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), U) ≃ₗ[Γ(X, V)]
        Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), V),
      ∀ m : Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), U),
        e ((1 : Γ(X, V)) ⊗ₜ[Γ(X, U)] m) =
          ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hVU).op m := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_baseChange_sections_linearEquiv_pushforward_tensorUnit_of_affineOpen_le.solution
