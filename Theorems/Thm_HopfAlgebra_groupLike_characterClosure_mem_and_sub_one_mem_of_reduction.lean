import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_FiniteFlat_SchematicClosure
import Definitions.Def_FiniteFlat_ClosureHopf
import Definitions.Def_FiniteFlat_ClosureHopfAlgebra
import Definitions.Def_HopfAlgebra_CharacterClosure
import P2M.Util
import P2M.Sol.S_HopfAlgebra_groupLike_characterClosure_mem_and_sub_one_mem_of_reduction

set_option autoImplicit false

open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem HopfAlgebra.groupLike_characterClosure_mem_and_sub_one_mem_of_reduction
    (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O]
    (F : Type) [Field F] [Algebra O F] [IsFractionRing O F]
    (A : Type) [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
    [Coalgebra.IsCocomm O A]
    (L : Type) [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀)
    (hvO : ∀ r : O, v (algebraMap O L r) ≤ 1)
    (S : Submonoid (WithConv (TensorProduct O F A →ₐ[F] L))) [Finite ↥S]
    (hsep : ∀ x : TensorProduct F (HopfAlgebra.pointQuot S) (HopfAlgebra.pointQuot S),
      (∀ (ν ν' : TensorProduct O F A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
        HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) → x = 0)
    (hinv : ∀ ν ∈ HopfAlgebra.ptSet S, ∃ ν' ∈ HopfAlgebra.ptSet S,
      ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F))
    (hev : Function.Bijective (HopfAlgebra.evalQuot S))
    (hred : ∀ ν ∈ HopfAlgebra.ptSet S, ∀ a : A,
      v (ν ((1 : F) ⊗ₜ[O] a) - algebraMap O L (Coalgebra.counit (R := O) a)) < 1)
    (hB : IsComulStable O F (HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S)))
    (hB' : IsAntipodeStable O F (HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S))) :
    letI := closureHopfAlgebra O F hB hB'
    (∀ d : TensorProduct O L ↥(HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S)),
      IsGroupLikeElem L d →
        d ∈ Submodule.span ↥v.valuationSubring
              (Set.range fun e : ↥(HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S)) => (1 : L) ⊗ₜ[O] e) ∧
        d - 1 ∈ (IsLocalRing.maximalIdeal ↥v.valuationSubring) •
              Submodule.span ↥v.valuationSubring
                (Set.range fun e : ↥(HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S)) => (1 : L) ⊗ₜ[O] e)) ∧
    (∀ f : CartierDual O ↥(HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S)), f * f = f → f = 0 ∨ f = 1) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_groupLike_characterClosure_mem_and_sub_one_mem_of_reduction.solution
