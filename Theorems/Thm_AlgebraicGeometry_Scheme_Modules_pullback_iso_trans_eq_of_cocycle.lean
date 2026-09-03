import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_pullback_iso_trans_eq_of_cocycle

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.pullback_iso_trans_eq_of_cocycle
    (X' X'' X''' : Scheme.{u}) (a₁ a₂ : X'' ⟶ X') (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')
    (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁) (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁) (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂)
    (L' : X'.Modules)
    (ψ : (Scheme.Modules.pullback a₁).obj L' ≅ (Scheme.Modules.pullback a₂).obj L')
    (hψ : ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L') ≪≫
          ((Scheme.Modules.pullbackCongr h₂).app L') ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₃).app L').symm
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app L')) :
    (((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ (((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso (Iso.refl ((Scheme.Modules.pullback a₁).obj L')) ≪≫ (Iso.refl ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))))
        = (((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso (Iso.refl ((Scheme.Modules.pullback a₁).obj L')) ≪≫ (((Scheme.Modules.pullbackComp b₁₃ a₁).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm))) ∧
    (((Scheme.Modules.pullbackCongr h₂).app L').symm ≪≫ (((Scheme.Modules.pullbackComp b₁₂ a₂).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ.symm ≪≫ (Iso.refl ((Scheme.Modules.pullback b₁₂).obj ((Scheme.Modules.pullback a₁).obj L'))))
        = (((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso (Iso.refl ((Scheme.Modules.pullback a₁).obj L')) ≪≫ (((Scheme.Modules.pullbackComp b₂₃ a₁).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₂).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ.symm))) ∧
    (((Scheme.Modules.pullbackCongr h₃).app L').symm ≪≫ (((Scheme.Modules.pullbackComp b₁₃ a₂).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso ψ.symm ≪≫ (((Scheme.Modules.pullbackComp b₁₃ a₁).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm))
        = (((Scheme.Modules.pullbackComp b₂₃ a₂).app L').symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso ψ.symm ≪≫ (((Scheme.Modules.pullbackComp b₂₃ a₁).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₂).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ.symm))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_pullback_iso_trans_eq_of_cocycle.solution
