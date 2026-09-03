import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import P2M.Util
import P2M.Sol.S_QuaternionAlgebra_finite_embeddingDatum

open scoped Quaternion

theorem QuaternionAlgebra.finite_embeddingDatum
    {a b : ℚ} (ha : a < 0) (hb : b < 0) (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hfg : Λ.FG) (t n : ℤ) :
    Finite (QuaternionAlgebra.EmbeddingDatum Λ t n) := by p2m_exact_reverting @_root_.P2MW.S_QuaternionAlgebra_finite_embeddingDatum.solution
