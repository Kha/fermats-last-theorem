import Mathlib
import Definitions.Def_GaloisRep_AdZeroMatrixGlue
import Definitions.Def_Deformations_TaylorWilesLocal
import Definitions.Def_TaylorWiles_Primes
import P2M.Util
import P2M.Sol.S_ResidualGaloisRep_finrank_ker_adZeroRep_sub_one_eq_one_of_charpoly_eq

open Module TaylorWiles
theorem ResidualGaloisRep.finrank_ker_adZeroRep_sub_one_eq_one_of_charpoly_eq
    {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (ρbar : ResidualGaloisRep k)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {α β : k} (hαβ : α ≠ β)
    (hchar : LinearMap.charpoly (ρbar.ρ σ) = (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)) :
    Module.finrank k (LinearMap.ker (ρbar.adZeroRep σ - 1)) = 1 := by p2m_exact_reverting @_root_.P2MW.S_ResidualGaloisRep_finrank_ker_adZeroRep_sub_one_eq_one_of_charpoly_eq.solution
