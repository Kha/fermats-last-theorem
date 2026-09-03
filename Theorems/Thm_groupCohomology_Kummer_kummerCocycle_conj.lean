import Mathlib
import Definitions.Def_GroupCohomology_Kummer
import P2M.Util
import P2M.Sol.S_groupCohomology_Kummer_kummerCocycle_conj

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer
theorem groupCohomology.Kummer.kummerCocycle_conj
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (α : Ωˣ) (g σ : Ω ≃ₐ[k] Ω) :
    kummerCocycle (g • α) (g * σ * g⁻¹) = g • kummerCocycle α σ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_Kummer_kummerCocycle_conj.solution
