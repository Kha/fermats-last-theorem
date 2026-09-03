import Mathlib
import Definitions.Def_ModularCurve_X1
import P2M.Util
import P2M.Sol.S_ModularCurve_XOneP_exists_ringHom_zmod_castHom_comp_eq_algebraMap_of_isCyclotomicExtension

set_option autoImplicit false

theorem ModularCurve.XOneP.exists_ringHom_zmod_castHom_comp_eq_algebraMap_of_isCyclotomicExtension
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (k : Type) [Field k] [CharP k p] [Algebra A k] :
    ∃ r : A →+* ZMod p, (ZMod.castHom (dvd_refl p) k).comp r = algebraMap A k := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XOneP_exists_ringHom_zmod_castHom_comp_eq_algebraMap_of_isCyclotomicExtension.solution
