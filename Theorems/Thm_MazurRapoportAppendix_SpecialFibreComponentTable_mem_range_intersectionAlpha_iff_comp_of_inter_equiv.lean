import Mathlib
import Definitions.Def_AlgebraicGeometry_MazurRapoportAppendixPicNeronCarriers
import P2M.Util
import P2M.Sol.S_MazurRapoportAppendix_SpecialFibreComponentTable_mem_range_intersectionAlpha_iff_comp_of_inter_equiv

set_option autoImplicit false

open MazurRapoportAppendix
open scoped BigOperators

theorem MazurRapoportAppendix.SpecialFibreComponentTable.mem_range_intersectionAlpha_iff_comp_of_inter_equiv
    {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (t : SpecialFibreComponentTable ι) (t' : SpecialFibreComponentTable ι') (Φ : ι ≃ ι')
    (hΦ : ∀ a b, t'.inter (Φ a) (Φ b) = t.inter a b) (f : ι' → ℤ) :
    f ∈ (intersectionAlpha t').range ↔ (f ∘ Φ) ∈ (intersectionAlpha t).range := by p2m_exact_reverting @_root_.P2MW.S_MazurRapoportAppendix_SpecialFibreComponentTable_mem_range_intersectionAlpha_iff_comp_of_inter_equiv.solution
