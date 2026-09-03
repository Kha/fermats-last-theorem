import Mathlib
import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isOrdinaryAt_of_isOrdinaryAt_baseChangeAlong_of_injective
attribute [-instance] CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree
attribute [-simp] CuspForm.HeckeGaloisRepDatum.mk.sizeOf_spec CuspForm.HeckeGaloisRepDatum.mk.injEq CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem GaloisRepAdic.isOrdinaryAt_of_isOrdinaryAt_baseChangeAlong_of_injective
    {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsLocalRing B] [IsDomain B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (hinj : Function.Injective φ)
    (ρ : GaloisRepAdic A) (p : ℕ)
    (hram : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∃ σ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ σ ≠ 1)
    (h : (ρ.baseChangeAlong φ hφ).IsOrdinaryAt p) :
    ρ.IsOrdinaryAt p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isOrdinaryAt_of_isOrdinaryAt_baseChangeAlong_of_injective.solution
