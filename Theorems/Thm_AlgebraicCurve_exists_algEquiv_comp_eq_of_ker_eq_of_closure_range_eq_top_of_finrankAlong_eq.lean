import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_algEquiv_comp_eq_of_ker_eq_of_closure_range_eq_top_of_finrankAlong_eq

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_algEquiv_comp_eq_of_ker_eq_of_closure_range_eq_top_of_finrankAlong_eq
    {K E R F F' : Type*} [Field K] [Field E] [CommRing R] [Field F] [Field F']
    [Algebra K E] [Algebra K R] [Algebra K F] [Algebra K F']
    (j : E →ₐ[K] R) (α : R →ₐ[K] F) (β : R →ₐ[K] F')
    (hker : RingHom.ker α.toRingHom = RingHom.ker β.toRingHom)
    (hgen : Subfield.closure (Set.range α) = ⊤)
    (hfin : FiniteAlong K (α.comp j)) (hfin' : FiniteAlong K (β.comp j))
    (hdeg : finrankAlong K (α.comp j) = finrankAlong K (β.comp j)) :
    ∃ ι : F ≃ₐ[K] F', (ι : F →ₐ[K] F').comp α = β := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_algEquiv_comp_eq_of_ker_eq_of_closure_range_eq_top_of_finrankAlong_eq.solution
