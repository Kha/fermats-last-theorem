import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_exists_conj_torus_eq_torus_pow

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.exists_conj_torus_eq_torus_pow (q : ℕ) [Fact q.Prime] :
    ∃ f : GL2 q, ∀ α : (GaloisField q 2)ˣ, f * torus q α * f⁻¹ = torus q (α ^ q) := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_exists_conj_torus_eq_torus_pow.solution
