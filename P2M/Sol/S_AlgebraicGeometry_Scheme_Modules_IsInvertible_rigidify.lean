import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_rigidify

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry"

theorem solution
    {T P : Scheme.{u}} {σ : T ⟶ P} {q : P ⟶ T} (hσq : σ ≫ q = 𝟙 T) {L : P.Modules}
    (hL : Scheme.Modules.IsInvertible L) :
    Scheme.Modules.IsInvertible (Scheme.Modules.rigidify σ q L) ∧
      Nonempty ((Scheme.Modules.pullback σ).obj (Scheme.Modules.rigidify σ q L) ≅ 𝟙_ T.Modules) := by

  have hσL : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback σ).obj L) :=
    Scheme.Modules.IsInvertible.pullback σ hL
  obtain ⟨hM, ⟨pairing⟩⟩ := Scheme.Modules.IsInvertible.dual hσL
  refine ⟨hL.tensor (Scheme.Modules.IsInvertible.pullback q hM), ⟨?_⟩⟩
  let M := Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L)

  let e : (Scheme.Modules.pullback σ).obj ((Scheme.Modules.pullback q).obj M) ≅ M :=
    (Scheme.Modules.pullbackComp σ q).app M ≪≫
      (Scheme.Modules.pullbackCongr hσq).app M ≪≫ (Scheme.Modules.pullbackId (X := T)).app M
  exact Scheme.Modules.pullbackTensorObjIso σ L _ ≪≫ (Iso.refl _ ⊗ᵢ e) ≪≫ pairing
