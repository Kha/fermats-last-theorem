import Mathlib
import Definitions.Def_GaloisRep_GlobalUnramifiedAt
import Definitions.Def_EllipticCurve_FrobeniusTrace
import P2M.Util
import P2M.Sol.S_GlobalGaloisRep_exists_finset_forall_isUnramifiedAt_of_isOpen_ker

theorem GlobalGaloisRep.exists_finset_forall_isUnramifiedAt_of_isOpen_ker
    {G : Type*} [Group G] (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* G)
    (hker : IsOpen ((ρ.ker : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) :
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → GlobalGaloisRep.IsUnramifiedAt ρ p := by p2m_exact_reverting @_root_.P2MW.S_GlobalGaloisRep_exists_finset_forall_isUnramifiedAt_of_isOpen_ker.solution
