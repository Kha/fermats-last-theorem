import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import P2M.Util
import P2M.Sol.S_PowerSeries_exists_isUnit_mul_eq_prod_X_sub_C_of_span_eq

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  WeierstrassCurve.DrinfeldGlobal

theorem PowerSeries.exists_isUnit_mul_eq_prod_X_sub_C_of_span_eq
    {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] {ι : Type*} (S : Finset ι) (z : ι → T)
    (hz : ∀ i ∈ S, z i ∈ IsLocalRing.maximalIdeal T) (x : PowerSeries T)
    (h : Ideal.span {x} = Ideal.span {∏ i ∈ S, (PowerSeries.X - PowerSeries.C (z i))}) :
    ∃ u : PowerSeries T, IsUnit u ∧ u * x = ∏ i ∈ S, (PowerSeries.X - PowerSeries.C (z i)) := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_exists_isUnit_mul_eq_prod_X_sub_C_of_span_eq.solution
