import Mathlib
import Definitions.Def_AlgebraicGeometry_CoherentBaseChange
import P2M.Util
import P2M.Sol.S_CoherentBaseChange_TwoTermComplex_natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi

universe u v w

open scoped TensorProduct
open CoherentBaseChange
theorem CoherentBaseChange.TwoTermComplex.natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi
    {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, v} R)
    (K : Type w) [Field K] [Algebra R K] :
    (Module.finrank K (LinearMap.ker (G.d.baseChange K)) : ℤ) -
      Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange K)) = G.chi := by p2m_exact_reverting @_root_.P2MW.S_CoherentBaseChange_TwoTermComplex_natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi.solution
