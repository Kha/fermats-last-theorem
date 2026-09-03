import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import P2M.Util
import P2M.Sol.S_CategoryTheory_ShortComplex_ShortExact_extClass_eq_zero_iff_exists_section_g
universe w v u
open CategoryTheory Abelian Limits
theorem CategoryTheory.ShortComplex.ShortExact.extClass_eq_zero_iff_exists_section_g
    {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C]
    [CategoryTheory.HasExt.{w} C] {S : CategoryTheory.ShortComplex C} (hS : S.ShortExact) :
    hS.extClass = 0 ↔ ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 S.X₃ := by p2m_exact_reverting @_root_.P2MW.S_CategoryTheory_ShortComplex_ShortExact_extClass_eq_zero_iff_exists_section_g.solution
