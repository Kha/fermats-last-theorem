import Definitions.Def_HeckeEis_DegeneracyTransfers
import P2M.Util
import P2M.Sol.S_HeckeEis_degeneracyTransferZero_heckeOperatorHom_comm

set_option autoImplicit false
open CongruenceSubgroup HeckeEis

theorem HeckeEis.degeneracyTransferZero_heckeOperatorHom_comm (N q' : ℕ) [NeZero N] [NeZero q']
    (hq' : q'.Prime) (hq'N : ¬ q' ∣ N) :
    ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N * q' →
      ∀ x : Additive (Gamma0 (N * q')) →+ ℤ,
        degeneracyTransfer₀ N q' ℤ hq' hq'N (heckeOperatorHom (N * q') ℓ ℤ x) =
          heckeOperatorHom N ℓ ℤ (degeneracyTransfer₀ N q' ℤ hq' hq'N x) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_degeneracyTransferZero_heckeOperatorHom_comm.solution
