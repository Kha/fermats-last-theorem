import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
import P2M.Sol.S_ModularCurve_XOneP_ofAlgAut_smul_diamondAutBar_smul_eq_diamondAutBar_smul_ofAlgAut_smul_place_of_diamondConj_x1_mul

set_option autoImplicit false

open AlgebraicCurve

theorem ModularCurve.XOneP.ofAlgAut_smul_diamondAutBar_smul_eq_diamondAutBar_smul_ofAlgAut_smul_place_of_diamondConj_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    [Algebra L (AlgebraicClosure ℚ)]

    (σ : ↥K ≃ₐ[L] ↥K)
    (σbar : ↥(ModularCurve.x1FunctionFieldBar (M * p)) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.x1FunctionFieldBar (M * p)))
    (hσbar : ∀ (f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (b : ↥K),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L) →
      ((σbar f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((σ b : ↥K) : LaurentSeries L))

    (d d' : ℕ) (hd : d.Coprime (M * p)) (hd' : d'.Coprime (M * p))
    (hdM : (d' : ZMod M) = (d : ZMod M)) (hdp : (d' : ZMod p) * (d : ZMod p) = 1)

    (θd θd' : ↥K ≃ₐ[L] ↥K)
    (hθd : ∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
      (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θd x : ↥K) : LaurentSeries L) =
          ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d) x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L))
    (hθd' : ∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
      (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θd' x : ↥K) : LaurentSeries L) =
          ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d') x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L))

    (hθdbar : ∀ (f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (b : ↥K),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L) →
      ((ModularCurve.diamondAutBar (M * p) d f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((θd b : ↥K) : LaurentSeries L))
    (hθd'bar : ∀ (f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) (b : ↥K),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((b : ↥K) : LaurentSeries L) →
      ((ModularCurve.diamondAutBar (M * p) d' f : ↥(ModularCurve.x1FunctionFieldBar (M * p))) : LaurentSeries (AlgebraicClosure ℚ)) =
        ModularCurve.coeffMap (algebraMap L (AlgebraicClosure ℚ)) ((θd' b : ↥K) : LaurentSeries L))

    (hconj : ∀ x : ↥K, ((σ (θd (σ.symm x)) : ↥K) : LaurentSeries L) = ((θd' x : ↥K) : LaurentSeries L)) :
    ∀ P : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)),
      AlgebraicCurve.SemilinearAut.ofAlgAut σbar • (AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutBar (M * p) d) • P) =
        AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondAutBar (M * p) d') • (AlgebraicCurve.SemilinearAut.ofAlgAut σbar • P) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_XOneP_ofAlgAut_smul_diamondAutBar_smul_eq_diamondAutBar_smul_ofAlgAut_smul_place_of_diamondConj_x1_mul.solution
