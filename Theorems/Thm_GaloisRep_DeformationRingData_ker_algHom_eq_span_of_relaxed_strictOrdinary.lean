import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_StrictOrdinary
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import P2M.Util
import P2M.Sol.S_GaloisRep_DeformationRingData_ker_algHom_eq_span_of_relaxed_strictOrdinary
attribute [-instance] CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree CuspForm.heckeLocal.instIsLocalizationAtPrime CuspForm.heckeLocal.instIsLocalization CuspForm.heckeBaseAlgebra.instAlgebra CuspForm.heckeLocal.instIsLocalRing CuspForm.heckeLocal.instIsNoetherianRing CuspForm.heckeLocal.instCommRing CuspForm.heckeLocalIdeal.instIsMaximal CuspForm.heckeLocal.instIsAdicComplete CuspForm.heckeLatticeAlgebra.instModuleFinite CuspForm.heckeCharKernel.instIsMaximal CuspForm.heckeLocal.instModuleFree CuspForm.heckeBaseAlgebra.instCommRing CuspForm.heckeLocal.instIsScalarTower CuspForm.heckeLatticeAlgebra.instModuleFree CuspForm.heckeLocal.instAlgebra CuspForm.heckeCharKernel.instIsPrime CuspForm.heckeLocal.instModuleFinite CuspForm.heckeLatticeAlgebra.instCommRing CuspForm.heckeLocal.instIsLocalHom CuspForm.heckeLocal.instAlgebraBase TateModule.instModule TateModule.instSMul Algebra.PatchingLevel.instModule Algebra.PatchingLevel.instAddCommGroup
attribute [-simp] CuspForm.HeckeGaloisRepDatum.mk.sizeOf_spec CuspForm.HeckeGaloisRepDatum.mk.injEq CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply Algebra.PatchingDatum.mk.injEq Algebra.PatchingLevel.mk.sizeOf_spec Algebra.PatchingDatum.mk.sizeOf_spec Algebra.PatchingLevel.mk.injEq
set_option autoImplicit false
open IsLocalRing Polynomial

theorem GaloisRep.DeformationRingData.ker_algHom_eq_span_of_relaxed_strictOrdinary
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    (p : ℕ) (Smin Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime ∧ q ∉ Smin) {ρbar : ResidualGaloisRep (ResidueField 𝒪)}
    (Dmin : GaloisRep.DeformationRingData 𝒪 ρbar (GaloisRep.minimalStrictOrdinaryCondition 𝒪 p Smin))
    (DQ : GaloisRep.DeformationRingData 𝒪 ρbar (fun _A _ _ _ ρ =>
        GaloisRep.strictOrdinaryCondition 𝒪 p (Smin ∪ Q) ρ ∧
          ∀ q ∈ Smin, q.Prime → q ≠ p → ρ.IsUnipotentOnInertiaAt q))
    (ε : DQ.R →ₐ[𝒪] Dmin.R) (hε : IsLocalHom (ε : DQ.R →+* Dmin.R))
    (hερ : (DQ.ρ.baseChangeAlong (ε : DQ.R →+* Dmin.R) hε).IsEquiv Dmin.ρ)
    (k : ℕ → ℕ)
    (cyc : (q : ℕ) → ((AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ))
    (hcyc : ∀ q ∈ Q, ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ), μ ^ q = 1 →
      σ μ = μ ^ ((cyc q σ : ZMod q).val))
    (πΔ : (q : ℕ) → ((ZMod q)ˣ →* Multiplicative (ZMod (p ^ k q))))
    (hπΔ : ∀ q ∈ Q, Function.Surjective (πΔ q))
    (χ : (q : ℕ) → (Multiplicative (ZMod (p ^ k q)) →* DQ.Rˣ))
    (hχ : ∀ q ∈ Q, ∀ (P : ValuationSubring (AlgebraicClosure ℚ)), P.LiesOverPrime q →
      ∃ b : Module.Basis (Fin 2) DQ.R DQ.ρ.V, ∀ σ ∈ P.inertiaSubgroupIn ℚ,
        DQ.ρ.ρ σ (b 0) = ((χ q (πΔ q (cyc q σ)) : DQ.Rˣ) : DQ.R) • b 0 ∧
        DQ.ρ.ρ σ (b 1) = (((χ q (πΔ q (cyc q σ)))⁻¹ : DQ.Rˣ) : DQ.R) • b 1)
    (ι : MonoidAlgebra 𝒪 (Π q : Q, Multiplicative (ZMod (p ^ k q))) →ₐ[𝒪] DQ.R)
    (hι : ∀ g : (Π q : Q, Multiplicative (ZMod (p ^ k q))),
      ι (MonoidAlgebra.of 𝒪 _ g) = ∏ q : Q, ((χ q (g q) : DQ.Rˣ) : DQ.R)) :
    RingHom.ker (ε : DQ.R →+* Dmin.R) =
      Ideal.span (Set.range fun g : (Π q : Q, Multiplicative (ZMod (p ^ k q))) => ι (MonoidAlgebra.of 𝒪 _ g) - 1) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_DeformationRingData_ker_algHom_eq_span_of_relaxed_strictOrdinary.solution
