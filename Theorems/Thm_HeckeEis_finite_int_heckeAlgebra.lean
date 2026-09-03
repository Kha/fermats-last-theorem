import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_CuspForm_HeckeAlgebra
import P2M.Util
import P2M.Sol.S_HeckeEis_finite_int_heckeAlgebra

set_option autoImplicit false

open scoped Manifold MatrixGroups

theorem HeckeEis.finite_int_heckeAlgebra (N : ℕ) [NeZero N] (n : ℕ) (S : Set ℕ)
    (hS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S) :
    Module.Finite ℤ ↥(CuspForm.heckeAlgebra N ((n : ℤ) + 2) S) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_finite_int_heckeAlgebra.solution
