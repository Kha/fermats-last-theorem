import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_compl_basicOpen_sub_sup_basicOpen_one_sub_mul_of_twoCharts

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.compl_basicOpen_sub_sup_basicOpen_one_sub_mul_of_twoCharts
    {X : Scheme.{u}} (U V : X.Opens)
    (f : Γ(X, U)) (g : Γ(X, V))
    (hg : U ⊓ V = X.basicOpen g)
    (hfg : (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (hUV : U ⊔ V = ⊤) (s : Γ(X, ⊤)) :
    ((X.basicOpen (f - (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s) ⊔
        X.basicOpen (1 - (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom s * g) : X.Opens) : Set X)ᶜ =
      (U : Set X) ∩ (X.basicOpen (f - (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s) : Set X)ᶜ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_compl_basicOpen_sub_sup_basicOpen_one_sub_mul_of_twoCharts.solution
