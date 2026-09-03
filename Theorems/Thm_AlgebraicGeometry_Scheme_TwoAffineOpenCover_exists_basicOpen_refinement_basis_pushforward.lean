import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_basicOpen_refinement_basis_pushforward
    {X Y : Scheme.{u}} (π : Y ⟶ X) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ x : X, π.finrank x = d)
    [IsIntegral X]

    (hX : ∀ Z : Set X, IsClosed Z → Z ≠ Set.univ → Z.Finite)
    (𝒱 : X.TwoAffineOpenCover) (h₀ : (𝒱.U0 : Set X).Nonempty) (h₁ : (𝒱.U1 : Set X).Nonempty) :
    ∃ (f₀ : Γ(X, 𝒱.U0)) (f₁ : Γ(X, 𝒱.U1)) (𝒱' : X.TwoAffineOpenCover),
      𝒱'.U0 = X.basicOpen f₀ ∧ 𝒱'.U1 = X.basicOpen f₁ ∧
      (∃ e : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), 𝒱'.U0),
        ∀ (W : X.Opens) (hW : W ≤ 𝒱'.U0),
          ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), W),
            ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hW).op (e i)) ∧
      (∃ e : Fin d → Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), 𝒱'.U1),
        ∀ (W : X.Opens) (hW : W ≤ 𝒱'.U1),
          ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules), W),
            ∀ i, b i = ((Scheme.Modules.pushforward π).obj (𝟙_ Y.Modules)).presheaf.map (homOfLE hW).op (e i)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_basicOpen_refinement_basis_pushforward.solution
