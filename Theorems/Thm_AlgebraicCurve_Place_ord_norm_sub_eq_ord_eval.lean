import Mathlib.RingTheory.Norm.Transitivity
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_ord_norm_sub_eq_ord_eval

open AlgebraicCurve

theorem AlgebraicCurve.Place.ord_norm_sub_eq_ord_eval {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra F F'] [Module.Finite F F'] (v : Place K F) (Q : Polynomial v.toValuationSubring) {x : F'} (hQ : Q.map (algebraMap v.toValuationSubring F) = minpoly F x) (hdeg : (minpoly F x).natDegree = Module.finrank F F') (b : v.toValuationSubring) : v.ord (Algebra.norm F (x - algebraMap F F' (b : F))) = v.ord ((Q.eval b : v.toValuationSubring) : F) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_ord_norm_sub_eq_ord_eval.solution
