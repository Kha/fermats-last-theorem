import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_genusFF_eq_and_nonempty_pic0_addEquiv_of_algebraMap_eq_comp

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.genusFF_eq_and_nonempty_pic0_addEquiv_of_algebraMap_eq_comp
    (k K F : Type*) [Field k] [Field K] [Field F] [Algebra K F] [Algebra k F]
    (e : k ≃+* K) (he : algebraMap k F = (algebraMap K F).comp e.toRingHom) :
    genusFF k F = genusFF K F ∧ Nonempty (Pic0 k F ≃+ Pic0 K F) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_genusFF_eq_and_nonempty_pic0_addEquiv_of_algebraMap_eq_comp.solution
