import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_of_ne_top

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_of_ne_top
    {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    (ι : F →+* F') (w : Place K' F')
    (hK : ∀ a : K, ι (algebraMap K F a) ∈ w.toValuationSubring)
    (hne : w.toValuationSubring.comap ι ≠ ⊤) :
    ∃ v : Place K F, v.toValuationSubring = w.toValuationSubring.comap ι := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_of_ne_top.solution
