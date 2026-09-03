import Mathlib
import P2M.Util
import P2M.Sol.S_LaurentSeries_exists_fg_subalgebra_isUnit_map_of_isUnit_map
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

universe u v

theorem LaurentSeries.exists_fg_subalgebra_isUnit_map_of_isUnit_map
    {A : Type u} {R : Type v} [CommRing A] [CommRing R] [Algebra A R]
    (x : LaurentSeries A) (hx : IsUnit (x.map (algebraMap A R))) :
    ∃ B : Subalgebra A R, B.FG ∧ IsUnit (x.map (algebraMap A B)) := by p2m_exact_reverting @_root_.P2MW.S_LaurentSeries_exists_fg_subalgebra_isUnit_map_of_isUnit_map.solution
