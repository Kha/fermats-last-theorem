import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app
    {X X₀ X₁ Y Y₀ Y₁ : Scheme.{u}}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X) (d : X₀ ⟶ X) (e : a ≫ b = d)
    (s₀ : Y₀ ⟶ X₀) (s₁ : Y₁ ⟶ X₁) (s : Y ⟶ X)
    (r : Y₀ ⟶ Y₁) (p : Y₁ ⟶ Y) (m : Y₀ ⟶ Y) (G : r ≫ p = m)
    (E : s₀ ≫ a = r ≫ s₁) (F : s₁ ≫ b = p ≫ s) (H : s₀ ≫ d = m ≫ s) (M : X.Modules) :
    (Scheme.Modules.pullbackComp s₀ a ≪≫ Scheme.Modules.pullbackCongr E ≪≫
          (Scheme.Modules.pullbackComp r s₁).symm).hom.app ((Scheme.Modules.pullback b).obj M) ≫
      (Scheme.Modules.pullback r).map
          ((Scheme.Modules.pullbackComp s₁ b ≪≫ Scheme.Modules.pullbackCongr F ≪≫
            (Scheme.Modules.pullbackComp p s).symm).hom.app M) ≫
        (Scheme.Modules.pullbackComp r p ≪≫ Scheme.Modules.pullbackCongr G).hom.app
          ((Scheme.Modules.pullback s).obj M) =
      (Scheme.Modules.pullback s₀).map
          ((Scheme.Modules.pullbackComp a b ≪≫ Scheme.Modules.pullbackCongr e).hom.app M) ≫
        (Scheme.Modules.pullbackComp s₀ d ≪≫ Scheme.Modules.pullbackCongr H ≪≫
          (Scheme.Modules.pullbackComp m s).symm).hom.app M := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app.solution
