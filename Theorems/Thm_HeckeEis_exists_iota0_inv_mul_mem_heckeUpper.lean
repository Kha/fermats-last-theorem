import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_IharaIota
import P2M.Util
import P2M.Sol.S_HeckeEis_exists_iota0_inv_mul_mem_heckeUpper

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.exists_iota0_inv_mul_mem_heckeUpper (N p ℓ : ℕ) (hℓ : Nat.Coprime ℓ (N * p))
    (γ : CongruenceSubgroup.Gamma0 N) :
    ∃ h : CongruenceSubgroup.Gamma0 (N * p), (Ihara.ι₀ N p h)⁻¹ * γ ∈ HeckeEis.heckeUpper N ℓ := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_exists_iota0_inv_mul_mem_heckeUpper.solution
