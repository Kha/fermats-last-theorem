import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_finrank_restrict_add_finrank_restrict_of_isCompl

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Hom.finrank_restrict_add_finrank_restrict_of_isCompl
    {Y S : Scheme.{u}} (f : Y ⟶ S) [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]
    (U V : Y.Opens) (hUV : U ⊔ V = ⊤) (hdisj : U ⊓ V = ⊥) (s : S) :
    (U.ι ≫ f).finrank s + (V.ι ≫ f).finrank s = f.finrank s := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_finrank_restrict_add_finrank_restrict_of_isCompl.solution
