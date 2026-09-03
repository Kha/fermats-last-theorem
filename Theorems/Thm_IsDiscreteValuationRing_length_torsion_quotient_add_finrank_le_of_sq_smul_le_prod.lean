import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_length_torsion_quotient_add_finrank_le_of_sq_smul_le_prod

set_option autoImplicit false

open Module

universe u

theorem IsDiscreteValuationRing.length_torsion_quotient_add_finrank_le_of_sq_smul_le_prod
    {R' : Type u} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    (π : R') (hπ : Irreducible π) (r n : ℕ)
    (N'' : Submodule R' ((Fin r → R') × (Fin n → R')))
    (hN : (Ideal.span {π ^ 2} : Ideal R') • N'' ≤ (⊤ : Submodule R' (Fin r → R')).prod ((Ideal.span {π} : Ideal R') • (⊤ : Submodule R' (Fin n → R')))) :
    Module.length R' (Submodule.torsion R' (((Fin r → R') × (Fin n → R')) ⧸ N'')) + Module.finrank R' N'' ≤
      Module.length R' (Submodule.torsion R'
        (↥((⊤ : Submodule R' (Fin r → R')).prod ((Ideal.span {π} : Ideal R') • (⊤ : Submodule R' (Fin n → R')))) ⧸
          ((Ideal.span {π ^ 2} : Ideal R') • N'').comap ((⊤ : Submodule R' (Fin r → R')).prod
            ((Ideal.span {π} : Ideal R') • (⊤ : Submodule R' (Fin n → R')))).subtype)) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_length_torsion_quotient_add_finrank_le_of_sq_smul_le_prod.solution
