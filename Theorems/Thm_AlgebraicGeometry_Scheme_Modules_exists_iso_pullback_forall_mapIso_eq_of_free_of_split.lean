import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_forall_mapIso_eq_of_free_of_split

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_forall_mapIso_eq_of_free_of_split
    {X Y : Scheme.{u}} (q : X ⟶ Y)
    (G : Type v) [AddGroup G] (σ : G → (X ⟶ X))
    (hσ0 : σ 0 = 𝟙 X) (hσadd : ∀ g h : G, σ (g + h) = σ g ≫ σ h)
    (hfree : ∀ ⦃Z : Scheme.{u}⦄ (v : Z ⟶ X) (g : G), Nonempty ↥Z → v ≫ σ g = v → g = 0)
    (hsplit : ∀ ⦃Z : Scheme.{u}⦄ (g₁ g₂ : Z ⟶ X), g₁ ≫ q = g₂ ≫ q →
      ∃ U : G → Z.Opens, ⨆ g, U g = ⊤ ∧ ∀ g, (U g).ι ≫ g₂ = (U g).ι ≫ g₁ ≫ σ g)
    (M : X.Modules)
    (ψ : ∀ g : G, M ≅ (Scheme.Modules.pullback (σ g)).obj M)
    {X'' : Scheme.{u}} (a₁ a₂ : X'' ⟶ X) (ha : a₁ ≫ q = a₂ ≫ q) :
    ∃ Ψ : (Scheme.Modules.pullback a₁).obj M ≅ (Scheme.Modules.pullback a₂).obj M,
      ∀ (g : G) ⦃W : Scheme.{u}⦄ (w : W ⟶ X'') (hw : (w ≫ a₁) ≫ σ g = w ≫ a₂),
        (Scheme.Modules.pullback w).mapIso Ψ =
          (Scheme.Modules.pullbackComp w a₁).app M ≪≫ (Scheme.Modules.pullback (w ≫ a₁)).mapIso (ψ g) ≪≫
            (Scheme.Modules.pullbackComp (w ≫ a₁) (σ g)).app M ≪≫ (Scheme.Modules.pullbackCongr hw).app M ≪≫
              ((Scheme.Modules.pullbackComp w a₂).app M).symm := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_forall_mapIso_eq_of_free_of_split.solution
