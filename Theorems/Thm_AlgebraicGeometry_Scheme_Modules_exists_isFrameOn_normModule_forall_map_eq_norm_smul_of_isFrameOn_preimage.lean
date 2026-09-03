import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_forall_map_eq_norm_smul_of_isFrameOn_preimage
attribute [-instance] SheafOfModules.isIso_ihomModelToIhom
attribute [-simp] PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_normModule_forall_map_eq_norm_smul_of_isFrameOn_preimage
    {X Y : Scheme.{u}} (π : Y ⟶ X) (d : ℕ) {ι : Type u} (U : ι → X.Opens)

    (e : ∀ i, Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), U i))
    (he : ∀ (i : ι) (W : X.Opens) (hW : W ≤ U i),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), W),
        ∀ k, b k = ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hW).op (e i k))

    (L : Y.Modules) (s : ∀ i, Γ(L, π ⁻¹ᵁ U i)) (hs : ∀ i, Scheme.Modules.IsFrameOn (s i) (π ⁻¹ᵁ U i))
    (u : ∀ i j, Γ(Y, π ⁻¹ᵁ (U i ⊓ U j)))
    (hu : ∀ i j, L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π inf_le_right)).op (s j) =
      u i j • L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π inf_le_left)).op (s i)) :
    ∃ Ω : ∀ i, Γ(Scheme.Modules.normModule π d L, U i),
      (∀ i, Scheme.Modules.IsFrameOn (Ω i) (U i)) ∧
      ∀ i j, letI : Algebra Γ(X, U i ⊓ U j) Γ(Y, π ⁻¹ᵁ (U i ⊓ U j)) := (π.app (U i ⊓ U j)).hom.toAlgebra
        (Scheme.Modules.normModule π d L).presheaf.map (homOfLE inf_le_right).op (Ω j) =
          (Algebra.norm Γ(X, U i ⊓ U j) (u i j)) •
            (Scheme.Modules.normModule π d L).presheaf.map (homOfLE inf_le_left).op (Ω i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_forall_map_eq_norm_smul_of_isFrameOn_preimage.solution
