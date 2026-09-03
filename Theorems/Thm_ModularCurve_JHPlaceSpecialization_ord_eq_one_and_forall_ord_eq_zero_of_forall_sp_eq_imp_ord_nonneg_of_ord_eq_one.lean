import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import P2M.Util
import P2M.Sol.S_ModularCurve_JHPlaceSpecialization_ord_eq_one_and_forall_ord_eq_zero_of_forall_sp_eq_imp_ord_nonneg_of_ord_eq_one

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.ord_eq_one_and_forall_ord_eq_zero_of_forall_sp_eq_imp_ord_nonneg_of_ord_eq_one
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Psp : JHPlaceSpecialization p M H hpM A)
    (T : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (y : LaurentSeries ↥A)
    (hy : coeffMap A.subtype y = ((T : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)))
    (Tbar : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))
    (hTbar : ((Tbar : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y)
    (hT0 : Tbar ≠ 0)
    (D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hD : ∀ v, D v = v.ord T)
    (w : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hreg : ∀ w', Psp.sp w' = Psp.sp w → 0 ≤ w'.ord T)
    (hw : 1 ≤ w.ord T)
    (hv : (Psp.sp w).ord Tbar = 1) :
    w.ord T = 1 ∧ ∀ w', Psp.sp w' = Psp.sp w → w' ≠ w → w'.ord T = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_JHPlaceSpecialization_ord_eq_one_and_forall_ord_eq_zero_of_forall_sp_eq_imp_ord_nonneg_of_ord_eq_one.solution
