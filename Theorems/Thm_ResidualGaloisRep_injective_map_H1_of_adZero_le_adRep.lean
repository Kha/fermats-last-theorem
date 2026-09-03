import Mathlib
import Definitions.Def_GaloisRep_AdZero
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_injective_map_H1_of_adZero_le_adRep

set_option autoImplicit false

open CategoryTheory groupCohomology

theorem ResidualGaloisRep.injective_map_H1_of_adZero_le_adRep
    {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (ρbar : ResidualGaloisRep k)
    {G : Type} [Group G] (f : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (φ : Rep.res f ρbar.adZero ⟶ Rep.res f (Rep.of ρbar.adRep))
    (hφ : ∀ x : LinearMap.ker (LinearMap.trace k ρbar.V), φ.hom x = (x : Module.End k ρbar.V)) :
    Function.Injective (groupCohomology.map (A := Rep.res f ρbar.adZero) (MonoidHom.id G) φ 1).hom := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_injective_map_H1_of_adZero_le_adRep.solution
