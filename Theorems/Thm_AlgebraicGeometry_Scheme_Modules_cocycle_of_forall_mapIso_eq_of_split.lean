import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_cocycle_of_forall_mapIso_eq_of_split

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.cocycle_of_forall_mapIso_eq_of_split
    {X Y : Scheme.{u}} (q : X ⟶ Y)
    (G : Type v) [AddGroup G] (σ : G → (X ⟶ X))
    (hσadd : ∀ g h : G, σ (g + h) = σ g ≫ σ h)
    (hsplit : ∀ ⦃Z : Scheme.{u}⦄ (g₁ g₂ : Z ⟶ X), g₁ ≫ q = g₂ ≫ q →
      ∃ U : G → Z.Opens, ⨆ g, U g = ⊤ ∧ ∀ g, (U g).ι ≫ g₂ = (U g).ι ≫ g₁ ≫ σ g)
    (M : X.Modules)
    (ψ : ∀ g : G, M ≅ (Scheme.Modules.pullback (σ g)).obj M)
    (hψadd : ∀ g h : G, ψ (g + h) =
        ψ g ≪≫ (Scheme.Modules.pullback (σ g)).mapIso (ψ h) ≪≫
          (Scheme.Modules.pullbackComp (σ g) (σ h)).app M ≪≫ ((Scheme.Modules.pullbackCongr (hσadd g h)).app M).symm)
    {X'' X''' : Scheme.{u}} (a₁ a₂ : X'' ⟶ X) (ha : a₁ ≫ q = a₂ ≫ q)
    (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')
    (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁) (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁) (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂)
    (Ψ : (Scheme.Modules.pullback a₁).obj M ≅ (Scheme.Modules.pullback a₂).obj M)
    (hΨ : ∀ (g : G) ⦃W : Scheme.{u}⦄ (w : W ⟶ X'') (hw : (w ≫ a₁) ≫ σ g = w ≫ a₂),
        (Scheme.Modules.pullback w).mapIso Ψ =
          (Scheme.Modules.pullbackComp w a₁).app M ≪≫ (Scheme.Modules.pullback (w ≫ a₁)).mapIso (ψ g) ≪≫
            (Scheme.Modules.pullbackComp (w ≫ a₁) (σ g)).app M ≪≫ (Scheme.Modules.pullbackCongr hw).app M ≪≫
              ((Scheme.Modules.pullbackComp w a₂).app M).symm) :
    ((Scheme.Modules.pullbackCongr h₁).app M).symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app M).symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso Ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app M) ≪≫
          ((Scheme.Modules.pullbackCongr h₂).app M) ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₁).app M).symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso Ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app M) ≪≫ ((Scheme.Modules.pullbackCongr h₃).app M).symm
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app M).symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso Ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app M) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_cocycle_of_forall_mapIso_eq_of_split.solution
