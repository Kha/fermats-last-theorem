import Mathlib
import Definitions.Def_GaloisRep_AdZero
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_trace_apply_eq_zero_of_mem_range_map_H1

set_option autoImplicit false

open CategoryTheory groupCohomology

theorem ResidualGaloisRep.trace_apply_eq_zero_of_mem_range_map_H1
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k)
    {G : Type} [Group G] (f : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (φ : Rep.res f ρbar.adZero ⟶ Rep.res f (Rep.of ρbar.adRep))
    (hφ : ∀ x : LinearMap.ker (LinearMap.trace k ρbar.V), φ.hom x = (x : Module.End k ρbar.V))
    (c : cocycles₁ (Rep.res f (Rep.of ρbar.adRep)))
    (hc : (H1π (Rep.res f (Rep.of ρbar.adRep))).hom c ∈
      LinearMap.range (groupCohomology.map (A := Rep.res f ρbar.adZero) (MonoidHom.id G) φ 1).hom)
    (σ : G) :
    LinearMap.trace k ρbar.V ((c : G → Module.End k ρbar.V) σ) = 0 := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_trace_apply_eq_zero_of_mem_range_map_H1.solution
