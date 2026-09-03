import Mathlib
import P2M.Util
import P2M.Sol.S_TopCat_Sheaf_isIso_of_isIso_app_of_isBasis

universe u v w u'

open CategoryTheory Opposite TopologicalSpace

theorem TopCat.Sheaf.isIso_of_isIso_app_of_isBasis {C : Type u} [Category.{v} C] {X : TopCat.{w}}
    {ι : Type u'} {B : ι → Opens X} (hB : Opens.IsBasis (Set.range B)) {F G : TopCat.Sheaf C X} (φ : F ⟶ G)
    (h : ∀ i, IsIso (φ.1.app (op (B i)))) : IsIso φ := by p2m_exact_reverting @_root_.P2MW.S_TopCat_Sheaf_isIso_of_isIso_app_of_isBasis.solution
