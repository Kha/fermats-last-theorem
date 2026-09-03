import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_of_forall_subsingleton_HSucc_baseChange_of_field
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_of_forall_subsingleton_HSucc_baseChange_of_field
    {K : Type u} [Field K] {X : Scheme.{u}} (π : X ⟶ Spec (.of K)) [IsSeparated π]
    (𝒰 : X.OrderedAffineCover) (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (K' : Type u) [Field K'] [Algebra K K']
    (h : ∀ i : ℕ, Subsingleton ((OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap K K'))
        ((Scheme.Modules.pullback (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap K K'))).obj M)).HSucc
        (𝒰.baseChange π K') i))
    (i : ℕ) :
    Subsingleton ((OModulePresheaf.ofModules π M).HSucc 𝒰 i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_of_forall_subsingleton_HSucc_baseChange_of_field.solution
