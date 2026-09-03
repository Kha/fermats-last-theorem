import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_FiniteFlat_SchematicClosure
import Definitions.Def_FiniteFlat_ClosureHopf
import Definitions.Def_FiniteFlat_ClosureHopfAlgebra
import Definitions.Def_HopfAlgebra_CharacterClosure
import P2M.Util
import P2M.Sol.S_HopfAlgebra_exists_characterClosure_points_equiv

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.exists_characterClosure_points_equiv
    (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O]
    (F : Type) [Field F] [Algebra O F] [IsFractionRing O F]
    (A : Type) [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
    [Coalgebra.IsCocomm O A]
    (L : Type) [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L] :
    ∃ χ : ∀ (S : Submonoid (WithConv (TensorProduct O F A →ₐ[F] L))) [Finite ↥S]
        (_ : (∀ x : TensorProduct F (HopfAlgebra.pointQuot S) (HopfAlgebra.pointQuot S),
          (∀ (ν ν' : TensorProduct O F A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
            HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) → x = 0))
        (_ : (∀ ν ∈ HopfAlgebra.ptSet S, ∃ ν' ∈ HopfAlgebra.ptSet S,
          ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)))
        (_ : Function.Bijective (HopfAlgebra.evalQuot S)),
        WithConv (↥(HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S)) →ₐ[O] L) ≃ (↥S →* L),
      (∀ (S : Submonoid (WithConv (TensorProduct O F A →ₐ[F] L))) [Finite ↥S]
          (hsep : (∀ x : TensorProduct F (HopfAlgebra.pointQuot S) (HopfAlgebra.pointQuot S),
          (∀ (ν ν' : TensorProduct O F A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
            HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) → x = 0))
          (hinv : (∀ ν ∈ HopfAlgebra.ptSet S, ∃ ν' ∈ HopfAlgebra.ptSet S,
          ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)))
          (hev : Function.Bijective (HopfAlgebra.evalQuot S))
          (hB : IsComulStable O F (HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S)))
          (hB' : IsAntipodeStable O F (HopfAlgebra.characterGenericFibre O F A L (HopfAlgebra.ptSet S))),
          letI := closureHopfAlgebra O F hB hB'
          ∀ ψ ψ' : WithConv (↥(HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S)) →ₐ[O] L),
            χ S hsep hinv hev (ψ * ψ') = χ S hsep hinv hev ψ * χ S hsep hinv hev ψ') ∧
      (∀ (S : Submonoid (WithConv (TensorProduct O F A →ₐ[F] L))) [Finite ↥S]
          (hsep : (∀ x : TensorProduct F (HopfAlgebra.pointQuot S) (HopfAlgebra.pointQuot S),
          (∀ (ν ν' : TensorProduct O F A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
            HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) → x = 0))
          (hinv : (∀ ν ∈ HopfAlgebra.ptSet S, ∃ ν' ∈ HopfAlgebra.ptSet S,
          ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)))
          (hev : Function.Bijective (HopfAlgebra.evalQuot S))
          (σ : L ≃ₐ[F] L) (ψ : WithConv (↥(HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S)) →ₐ[O] L)) (ν ν' : ↥S),
          (∀ x, (WithConv.ofConv ν'.1) x = σ ((WithConv.ofConv ν.1) x)) →
          χ S hsep hinv hev (WithConv.toConv (((σ : L →ₐ[F] L).restrictScalars O).comp (WithConv.ofConv ψ))) ν'
            = σ (χ S hsep hinv hev ψ ν)) ∧
      (∀ (S S' : Submonoid (WithConv (TensorProduct O F A →ₐ[F] L))) [Finite ↥S] [Finite ↥S']
          (hsep : (∀ x : TensorProduct F (HopfAlgebra.pointQuot S) (HopfAlgebra.pointQuot S),
          (∀ (ν ν' : TensorProduct O F A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
            HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) → x = 0))
          (hinv : (∀ ν ∈ HopfAlgebra.ptSet S, ∃ ν' ∈ HopfAlgebra.ptSet S,
          ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)))
          (hev : Function.Bijective (HopfAlgebra.evalQuot S))
          (hsep' : (∀ x : TensorProduct F (HopfAlgebra.pointQuot S') (HopfAlgebra.pointQuot S'),
          (∀ (ν ν' : TensorProduct O F A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S') (hν' : ν' ∈ HopfAlgebra.ptSet S'),
            HopfAlgebra.evalPair (HopfAlgebra.ptSet S') ν ν' hν hν' x = 0) → x = 0))
          (hinv' : (∀ ν ∈ HopfAlgebra.ptSet S', ∃ ν' ∈ HopfAlgebra.ptSet S',
          ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)))
          (hev' : Function.Bijective (HopfAlgebra.evalQuot S'))
          (hle : S ≤ S') (ψ : WithConv (↥(HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S')) →ₐ[O] L)) (ν : ↥S),
          χ S hsep hinv hev (WithConv.toConv ((WithConv.ofConv ψ).comp
              (Subalgebra.inclusion (HopfAlgebra.characterClosure_mono O F A L (HopfAlgebra.ptSet_mono hle))))) ν
            = χ S' hsep' hinv' hev' ψ ⟨ν.1, hle ν.2⟩) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_exists_characterClosure_points_equiv.solution
