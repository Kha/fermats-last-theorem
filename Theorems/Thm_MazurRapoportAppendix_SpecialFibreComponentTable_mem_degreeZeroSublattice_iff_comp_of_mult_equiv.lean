import Mathlib
import Definitions.Def_AlgebraicGeometry_MazurRapoportAppendixPicNeronCarriers
import P2M.Util
import P2M.Sol.S_MazurRapoportAppendix_SpecialFibreComponentTable_mem_degreeZeroSublattice_iff_comp_of_mult_equiv

set_option autoImplicit false

open MazurRapoportAppendix
open scoped BigOperators

theorem MazurRapoportAppendix.SpecialFibreComponentTable.mem_degreeZeroSublattice_iff_comp_of_mult_equiv
    {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (t : SpecialFibreComponentTable ι) (t' : SpecialFibreComponentTable ι') (Φ : ι ≃ ι')
    (hm : ∀ a, t'.mult (Φ a) = t.mult a) (f : ι' → ℤ) :
    f ∈ degreeZeroSublattice t' ↔ (f ∘ Φ) ∈ degreeZeroSublattice t := by p2m_exact_reverting @_root_.P2MW.S_MazurRapoportAppendix_SpecialFibreComponentTable_mem_degreeZeroSublattice_iff_comp_of_mult_equiv.solution
