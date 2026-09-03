import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_ramificationIndexAlong_eq_one_of_pow_eq_of_mem_of_inv_mem

set_option autoImplicit false

open Polynomial AlgebraicCurve

theorem AlgebraicCurve.Place.ramificationIndexAlong_eq_one_of_pow_eq_of_mem_of_inv_mem
    {k F F' : Type*} [Field k] [IsAlgClosed k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral)
    (n : ℕ) (hn : (n : k) ≠ 0)
    (c : F') (hgen : Subfield.closure (Set.range φ ∪ {c}) = ⊤)
    (u : F) (hu : φ u = c ^ n)
    (P : AlgebraicCurve.Place k F')
    (hrat : (P.restrictAlong φ hφ).IsRational)
    (huP : u ∈ (P.restrictAlong φ hφ).toValuationSubring ∧ u⁻¹ ∈ (P.restrictAlong φ hφ).toValuationSubring) :
    P.ramificationIndexAlong φ = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_ramificationIndexAlong_eq_one_of_pow_eq_of_mem_of_inv_mem.solution
