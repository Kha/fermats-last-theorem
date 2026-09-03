import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_twoAffineOpenCover_eq_basicOpen_sub_sup_of_twoCharts_of_isUnit_sub

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_twoAffineOpenCover_eq_basicOpen_sub_sup_of_twoCharts_of_isUnit_sub
    {X : Scheme.{u}} (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (f : Γ(X, U)) (g : Γ(X, V))
    (hf : U ⊓ V = X.basicOpen f) (hg : U ⊓ V = X.basicOpen g)
    (hfg : (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (hUV : U ⊔ V = ⊤) (s₀ s₁ : Γ(X, ⊤)) (hs : IsUnit (s₀ - s₁)) :
    ∃ 𝒲 : X.TwoAffineOpenCover,
      𝒲.U0 = X.basicOpen (f - (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s₀) ⊔
        X.basicOpen (1 - (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom s₀ * g) ∧
      𝒲.U1 = X.basicOpen (f - (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s₁) ⊔
        X.basicOpen (1 - (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom s₁ * g) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_twoAffineOpenCover_eq_basicOpen_sub_sup_of_twoCharts_of_isUnit_sub.solution
