import Mathlib
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_Correspondence
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_restrictAlong_congrEquiv_and_existsUnique_iff

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Place.restrictAlong_congrEquiv_and_existsUnique_iff
    {K E F F' : Type*} [Field K] [Field E] [Field F] [Field F'] [Algebra K E] [Algebra K F] [Algebra K F']
    (φ : E →ₐ[K] F) (hφ : φ.toRingHom.IsIntegral) (φ' : E →ₐ[K] F') (hφ' : φ'.toRingHom.IsIntegral)
    (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
    (hcomm : ∀ x : E, e (φ x) = φ' x) :
    (∀ w : Place K F, (Place.congrEquiv e he w).restrictAlong φ' hφ' = w.restrictAlong φ hφ) ∧
    (∀ s : Place K E, ∀ w' : Place K F', w'.restrictAlong φ' hφ' = s ↔
        ((Place.congrEquiv e he).symm w').restrictAlong φ hφ = s) ∧
    (∀ s : Place K E, (∃! w : Place K F, w.restrictAlong φ hφ = s) ↔
        (∃! w' : Place K F', w'.restrictAlong φ' hφ' = s)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_restrictAlong_congrEquiv_and_existsUnique_iff.solution
