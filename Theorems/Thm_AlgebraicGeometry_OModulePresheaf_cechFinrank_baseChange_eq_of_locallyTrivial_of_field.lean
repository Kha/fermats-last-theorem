import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_baseChange_eq_of_locallyTrivial_of_field
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.OModulePresheaf.cechFinrank_baseChange_eq_of_locallyTrivial_of_field
    {k₀ : Type u} [Field k₀] {X : Scheme.{u}} (π : X ⟶ Spec (.of k₀)) [IsSeparated π] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (𝒰 : X.OrderedAffineCover) (k : Type u) [Field k] [Algebra k₀ k] (n : ℕ) :
    (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap k₀ k))
        ((Scheme.Modules.pullback
          (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap k₀ k))).obj M)).cechFinrank (𝒰.baseChange π k) n =
      (OModulePresheaf.ofModules π M).cechFinrank 𝒰 n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinrank_baseChange_eq_of_locallyTrivial_of_field.solution
