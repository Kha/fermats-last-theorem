import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_semilinearAut_intertwinesAlong_heckeAlphaC_heckeBetaC_coeffSemilinearAut
set_option autoImplicit false
open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_semilinearAut_intertwinesAlong_heckeAlphaC_heckeBetaC_coeffSemilinearAut
    (N ℓ : ℕ) [NeZero N] [NeZero ℓ] {k : Type*} [Field k] (τ : k ≃+* k) :
    ∃ g' : SemilinearAut k ↥(charLDegeneracyRoof k N ℓ),
      SemilinearAut.IntertwinesAlong (heckeAlphaC k N ℓ).toRingHom (coeffSemilinearAut N τ) g' ∧
      SemilinearAut.IntertwinesAlong (heckeBetaC k N ℓ).toRingHom (coeffSemilinearAut N τ) g' := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_semilinearAut_intertwinesAlong_heckeAlphaC_heckeBetaC_coeffSemilinearAut.solution
