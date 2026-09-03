import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_descentData_obj_eq_of_cocycle_of_free_of_split

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_descentData_obj_eq_of_cocycle_of_free_of_split
    {X Y : Scheme.{u}} (q : X ⟶ Y)
    (G : Type v) [AddGroup G] (σ : G → (X ⟶ X))
    (hσ0 : σ 0 = 𝟙 X) (hσadd : ∀ g h : G, σ (g + h) = σ g ≫ σ h)
    (hfree : ∀ ⦃Z : Scheme.{u}⦄ (v : Z ⟶ X) (g : G), Nonempty ↥Z → v ≫ σ g = v → g = 0)
    (hsplit : ∀ ⦃Z : Scheme.{u}⦄ (g₁ g₂ : Z ⟶ X), g₁ ≫ q = g₂ ≫ q →
      ∃ U : G → Z.Opens, ⨆ g, U g = ⊤ ∧ ∀ g, (U g).ι ≫ g₂ = (U g).ι ≫ g₁ ≫ σ g)
    (M : X.Modules)
    (ψ : ∀ g : G, M ≅ (Scheme.Modules.pullback (σ g)).obj M)
    (hψ0 : ψ 0 = ((Scheme.Modules.pullbackId X).app M).symm ≪≫ ((Scheme.Modules.pullbackCongr hσ0).app M).symm)
    (hψadd : ∀ g h : G, ψ (g + h) =
        ψ g ≪≫ (Scheme.Modules.pullback (σ g)).mapIso (ψ h) ≪≫
          (Scheme.Modules.pullbackComp (σ g) (σ h)).app M ≪≫ ((Scheme.Modules.pullbackCongr (hσadd g h)).app M).symm) :
    ∃ D : ((Scheme.Modules.pseudofunctor.{u}).comp Bicategory.Adj.forget₁).DescentData (fun _ : Unit => q),
      ∀ i, D.obj i = M := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_descentData_obj_eq_of_cocycle_of_free_of_split.solution
