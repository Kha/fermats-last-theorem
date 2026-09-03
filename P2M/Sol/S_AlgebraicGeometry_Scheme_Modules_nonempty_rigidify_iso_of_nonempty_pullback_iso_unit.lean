import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_rigidify_iso_of_nonempty_pullback_iso_unit

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"

theorem solution
    {T P : Scheme.{u}} (σ : T ⟶ P) (q : P ⟶ T) (L : P.Modules)
    (hσL : Nonempty ((Scheme.Modules.pullback σ).obj L ≅ 𝟙_ T.Modules)) :
    Nonempty (Scheme.Modules.rigidify σ q L ≅ L) := by
  obtain ⟨e⟩ := hσL

  let u : ihom (𝟙_ T.Modules) ≅ 𝟭 T.Modules :=
    conjugateIsoEquiv (ihom.adjunction (𝟙_ T.Modules)) Adjunction.id (leftUnitorNatIso T.Modules).symm

  let d : Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L) ≅ 𝟙_ T.Modules :=
    Scheme.Modules.dualMapIso e ≪≫ u.app (𝟙_ T.Modules)
  refine ⟨?_⟩
  rw [Scheme.Modules.rigidify_def]
  exact whiskerLeftIso L ((Scheme.Modules.pullback q).mapIso d ≪≫ Scheme.Modules.pullbackTensorUnitObjIso q) ≪≫ ρ_ L
