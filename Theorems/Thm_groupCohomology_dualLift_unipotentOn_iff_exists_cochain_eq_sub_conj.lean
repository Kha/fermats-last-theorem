import Definitions.Def_GroupCohomology_TangentSpace
import P2M.Util
import P2M.Sol.S_groupCohomology_dualLift_unipotentOn_iff_exists_cochain_eq_sub_conj

set_option autoImplicit false
open groupCohomology

theorem groupCohomology.dualLift_unipotentOn_iff_exists_cochain_eq_sub_conj
    {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V]
    (hV : Module.finrank k V = 2)
    {G : Type} [Group G] (ρ₀ : G →* Module.End k V)
    (ρ : G →* (DualNumber (Module.End k V))ˣ) (hρ : IsDualLift ρ₀.toHomUnits ρ)
    (I : Subgroup G) (hcyc : IsCyclic (I.map ρ))
    (hne : ∃ g ∈ I, ρ₀ g ≠ 1) (hunip : ∀ g ∈ I, (ρ₀ g - 1) ^ 2 = 0) :
    (∀ g ∈ I, ((ρ g : DualNumber (Module.End k V)) - 1) ^ 2 = 0) ↔
      ∃ m : Module.End k V, ∀ g ∈ I,
        dualLiftToCochain ρ₀.toHomUnits ρ g = m - ρ₀ g * m * ρ₀ g⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_dualLift_unipotentOn_iff_exists_cochain_eq_sub_conj.solution
