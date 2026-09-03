import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_map_eq_norm_smul_of_isFrameOn_preimage
attribute [-instance] SheafOfModules.isIso_ihomModelToIhom
attribute [-simp] PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Modules.exists_isFrameOn_normModule_map_eq_norm_smul_of_isFrameOn_preimage
    {X Y : Scheme.{u}} (π : Y ⟶ X) (d : ℕ) (𝒰 : X.TwoAffineOpenCover)
    (e₀ : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), 𝒰.U0))
    (he₀ : ∀ (W : X.Opens) (hW : W ≤ 𝒰.U0),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hW).op (e₀ i))
    (e₁ : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), 𝒰.U1))
    (he₁ : ∀ (W : X.Opens) (hW : W ≤ 𝒰.U1),
      ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), W),
        ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hW).op (e₁ i))
    (L : Y.Modules) (s₀ : Γ(L, π ⁻¹ᵁ 𝒰.U0)) (s₁ : Γ(L, π ⁻¹ᵁ 𝒰.U1))
    (hs₀ : Scheme.Modules.IsFrameOn s₀ (π ⁻¹ᵁ 𝒰.U0)) (hs₁ : Scheme.Modules.IsFrameOn s₁ (π ⁻¹ᵁ 𝒰.U1))
    (u : Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)))
    (hs : L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π inf_le_right)).op s₁ =
      u • L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π inf_le_left)).op s₀) :
    letI : Algebra Γ(X, 𝒰.U0 ⊓ 𝒰.U1) Γ(Y, π ⁻¹ᵁ (𝒰.U0 ⊓ 𝒰.U1)) := (π.app (𝒰.U0 ⊓ 𝒰.U1)).hom.toAlgebra
    ∃ (Ω₀ : Γ(Scheme.Modules.normModule π d L, 𝒰.U0)) (Ω₁ : Γ(Scheme.Modules.normModule π d L, 𝒰.U1)),
      Scheme.Modules.IsFrameOn Ω₀ 𝒰.U0 ∧ Scheme.Modules.IsFrameOn Ω₁ 𝒰.U1 ∧
      (Scheme.Modules.normModule π d L).presheaf.map (homOfLE inf_le_right).op Ω₁ =
        (Algebra.norm Γ(X, 𝒰.U0 ⊓ 𝒰.U1) u) •
          (Scheme.Modules.normModule π d L).presheaf.map (homOfLE inf_le_left).op Ω₀ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_map_eq_norm_smul_of_isFrameOn_preimage.solution
