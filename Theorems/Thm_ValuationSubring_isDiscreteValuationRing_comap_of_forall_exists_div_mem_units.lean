import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_isDiscreteValuationRing_comap_of_forall_exists_div_mem_units

set_option autoImplicit false

universe u

theorem ValuationSubring.isDiscreteValuationRing_comap_of_forall_exists_div_mem_units
    {L : Type u} [Field L] {Ω : Type u} [Field Ω] [Algebra L Ω]
    (A : ValuationSubring Ω)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap L Ω)))
    (M : IntermediateField L Ω)
    (hval : ∀ x : Ω, x ∈ M → x ≠ 0 →
      ∃ c : L, c ≠ 0 ∧ x * (algebraMap L Ω c)⁻¹ ∈ A ∧ algebraMap L Ω c * x⁻¹ ∈ A) :
    IsDiscreteValuationRing ↥(A.comap (algebraMap ↥M Ω)) := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_isDiscreteValuationRing_comap_of_forall_exists_div_mem_units.solution
