import Mathlib
import Definitions.Def_GaloisRep_LocalConditions
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_isOrdinaryAt_of_stableLine_baseChange
attribute [-instance] CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree
attribute [-simp] CuspForm.HeckeGaloisRepDatum.mk.sizeOf_spec CuspForm.HeckeGaloisRepDatum.mk.injEq CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

open scoped TensorProduct
theorem GaloisRepAdic.isOrdinaryAt_of_stableLine_baseChange
    {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type) [Field K] [Algebra A K] [IsFractionRing A K]
    (ρ : GaloisRepAdic A) (p : ℕ)
    (h : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∃ L : Submodule K (K ⊗[A] ρ.V),
        Module.finrank K L = 1 ∧
        (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ w ∈ L, (ρ.ρ σ).baseChange K w ∈ L) ∧
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w : K ⊗[A] ρ.V, (ρ.ρ σ).baseChange K w - w ∈ L)) :
    ρ.IsOrdinaryAt p := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_isOrdinaryAt_of_stableLine_baseChange.solution
