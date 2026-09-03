import Mathlib
import Definitions.Def_GaloisRep_AdZero
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_finrank_invariants_res_adRep_eq_finrank_invariants_res_adZero_add_one

set_option autoImplicit false

open CategoryTheory groupCohomology

theorem ResidualGaloisRep.finrank_invariants_res_adRep_eq_finrank_invariants_res_adZero_add_one
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k) (h2 : (2 : k) ≠ 0)
    {G : Type} [Group G] (φ : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    Module.finrank k (Rep.res φ (Rep.of ρbar.adRep)).ρ.invariants =
      Module.finrank k (Rep.res φ ρbar.adZero).ρ.invariants + 1 := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_finrank_invariants_res_adRep_eq_finrank_invariants_res_adZero_add_one.solution
