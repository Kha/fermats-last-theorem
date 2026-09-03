import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_RegularProlongation_exists_mem_integers_iff_map_mem_and_residue_eq_of_algEquiv

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_mem_integers_iff_map_mem_and_residue_eq_of_algEquiv
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) (θ : F ≃ₐ[L] F) :
    ∃ R' : RegularProlongation A F Fbar,
      ∃ hmem : ∀ f : F, f ∈ R'.integers ↔ θ f ∈ R.integers,
        ∀ (f : F) (h : f ∈ R'.integers), R'.residue ⟨f, h⟩ = R.residue ⟨θ f, (hmem f).mp h⟩ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_RegularProlongation_exists_mem_integers_iff_map_mem_and_residue_eq_of_algEquiv.solution
