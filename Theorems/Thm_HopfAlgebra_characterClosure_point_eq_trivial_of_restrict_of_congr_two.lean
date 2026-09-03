import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_FiniteFlat_SchematicClosure
import Definitions.Def_FiniteFlat_ClosureHopf
import Definitions.Def_FiniteFlat_ClosureHopfAlgebra
import Definitions.Def_HopfAlgebra_CharacterClosure
import P2M.Util
import P2M.Sol.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two
attribute [-instance] CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

set_option autoImplicit false

open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem HopfAlgebra.characterClosure_point_eq_trivial_of_restrict_of_congr_two
    (O : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [IsNoetherianRing O]
    (h2 : Irreducible (2 : O))
    (F : Type) [Field F] [Algebra O F] [IsFractionRing O F]
    (A : Type) [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]
    [Coalgebra.IsCocomm O A]
    (L : Type) [Field L] [Algebra F L] [Algebra O L] [IsScalarTower O F L]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀)
    (hvO : ∀ r : O, v (algebraMap O L r) ≤ 1)
    (S S' : Submonoid (WithConv (TensorProduct O F A →ₐ[F] L))) [Finite ↥S] [Finite ↥S'] (hle : S ≤ S')
    (hindex : ∀ ν μ : WithConv (TensorProduct O F A →ₐ[F] L), ν ∈ S' → μ ∈ S' → ν ∉ S → μ ∉ S → ν * μ ∈ S)
    (hsep : ∀ x : TensorProduct F (HopfAlgebra.pointQuot S) (HopfAlgebra.pointQuot S),
      (∀ (ν ν' : TensorProduct O F A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
        HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) → x = 0)
    (hinv : ∀ ν ∈ HopfAlgebra.ptSet S, ∃ ν' ∈ HopfAlgebra.ptSet S,
      ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F))
    (hev : Function.Bijective (HopfAlgebra.evalQuot S))
    (hsep' : ∀ x : TensorProduct F (HopfAlgebra.pointQuot S') (HopfAlgebra.pointQuot S'),
      (∀ (ν ν' : TensorProduct O F A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S') (hν' : ν' ∈ HopfAlgebra.ptSet S'),
        HopfAlgebra.evalPair (HopfAlgebra.ptSet S') ν ν' hν hν' x = 0) → x = 0)
    (hinv' : ∀ ν ∈ HopfAlgebra.ptSet S', ∃ ν' ∈ HopfAlgebra.ptSet S',
      ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F))
    (hev' : Function.Bijective (HopfAlgebra.evalQuot S'))
    (hred' : ∀ ν ∈ HopfAlgebra.ptSet S', ∀ a : A,
      v (ν ((1 : F) ⊗ₜ[O] a) - algebraMap O L (Coalgebra.counit (R := O) a)) < 1)
    (ψ : ↥(HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S')) →ₐ[O] L)
    (hψS : ∀ e : ↥(HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S)),
      ψ (Subalgebra.inclusion
          (HopfAlgebra.characterClosure_mono O F A L (HopfAlgebra.ptSet_mono hle)) e)
        = algebraMap O L (Coalgebra.counit (R := O) (e : CartierDual O A)))
    (hψred : ∀ e : ↥(HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S')),
      v (ψ e - algebraMap O L (Coalgebra.counit (R := O) (e : CartierDual O A))) < 1) :
    ∀ e : ↥(HopfAlgebra.characterClosure O F A L (HopfAlgebra.ptSet S')),
      ψ e = algebraMap O L (Coalgebra.counit (R := O) (e : CartierDual O A)) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_characterClosure_point_eq_trivial_of_restrict_of_congr_two.solution
