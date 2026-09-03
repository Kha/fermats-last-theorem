import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull
set_option autoImplicit false
open AlgebraicGeometry
theorem ModularCurve.exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull
    {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R ℚ]
    (p : ℕ) [NeZero p]
    (M : AlgebraicCurve.CurveModel ℚ ↥(ModularCurve.modularFunctionFieldFull p))
    (x : closedPoints M.C) (hx : M.placeOfPoint x = ModularCurve.cuspInftyFull p)
    (ι : R →+* R') (π : R' →+* R) (hπ : π.comp ι = RingHom.id R)
    (t : R') (ht : π t = 0) (hcot : RingHom.ker π ≤ Ideal.span {t} ⊔ RingHom.ker π ^ 2)
    (route : R' →+* M.C.presheaf.stalk x.1)
    (hι : ∀ r : R, ((M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField (route (ι r))) :
        ↥(ModularCurve.modularFunctionFieldFull p)) : LaurentSeries ℚ) = HahnSeries.C (algebraMap R ℚ r))
    (hI : ∀ i ∈ RingHom.ker π, route i ∈ IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1))
    (u : PowerSeries R)
    (hu : ((M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField (route t)) :
        ↥(ModularCurve.modularFunctionFieldFull p)) : LaurentSeries ℚ) =
      HahnSeries.ofPowerSeries ℤ ℚ (u.map (algebraMap R ℚ)))
    (z : R') :
    ∃ P : PowerSeries R,
      ((M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField (route z)) :
          ↥(ModularCurve.modularFunctionFieldFull p)) : LaurentSeries ℚ) =
        HahnSeries.ofPowerSeries ℤ ℚ (P.map (algebraMap R ℚ)) ∧
      PowerSeries.constantCoeff P = π z := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_powerSeries_map_eq_ffEquiv_symm_of_placeOfPoint_eq_cuspInftyFull.solution
