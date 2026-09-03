import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_WeierstrassCurve_FormalGroup
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import P2M.Util
import P2M.Sol.S_PowerSeries_card_eq_of_isUnit_mul_eq_prod_X_sub_C_of_map_residue_eq_mul_X_pow

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory WeierstrassProjModel WeierstrassCurve.DrinfeldGlobal IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem PowerSeries.card_eq_of_isUnit_mul_eq_prod_X_sub_C_of_map_residue_eq_mul_X_pow
    {T : Type u} [CommRing T] [IsLocalRing T] {ι : Type*} (S : Finset ι) (z : ι → T)
    (hz : ∀ i ∈ S, z i ∈ maximalIdeal T) (f u : PowerSeries T) (hu : IsUnit u) (N : ℕ)
    (hf : ∃ v : PowerSeries (ResidueField T), IsUnit v ∧ PowerSeries.map (residue T) f = v * PowerSeries.X ^ N)
    (h : u * f = ∏ i ∈ S, (PowerSeries.X - PowerSeries.C (z i))) :
    S.card = N := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_card_eq_of_isUnit_mul_eq_prod_X_sub_C_of_map_residue_eq_mul_X_pow.solution
