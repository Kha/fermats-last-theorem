import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv
import Definitions.Def_Algebra_PatchingDatum
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import P2M.Util
import P2M.Sol.S_GaloisRep_DeformationRingData_algHom_inertiaCharacter_eq_one_of_forall_isUnramifiedAt

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open IsLocalRing Polynomial
theorem GaloisRep.DeformationRingData.algHom_inertiaCharacter_eq_one_of_forall_isUnramifiedAt
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    (p : ℕ) {ρbar : ResidualGaloisRep (ResidueField 𝒪)}
    {𝒟₀ 𝒟Q : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀) (DQ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟Q)
    {q : ℕ} (hq : q.Prime)
    (h₀ : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρ : GaloisRepAdic A), 𝒟₀ ρ → ρ.IsUnramifiedAt q)
    (ε : DQ.R →ₐ[𝒪] D₀.R) (hε : IsLocalHom (ε : DQ.R →+* D₀.R))
    (hερ : (DQ.ρ.baseChangeAlong (ε : DQ.R →+* D₀.R) hε).IsEquiv D₀.ρ)
    {k : ℕ}
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ), μ ^ q = 1 →
      σ μ = μ ^ ((cyc σ : ZMod q).val))
    (πΔ : (ZMod q)ˣ →* Multiplicative (ZMod (p ^ k))) (hπΔ : Function.Surjective πΔ)
    (χ : Multiplicative (ZMod (p ^ k)) →* DQ.Rˣ)
    (hχ : ∀ (P : ValuationSubring (AlgebraicClosure ℚ)), P.LiesOverPrime q →
      ∃ b : Module.Basis (Fin 2) DQ.R DQ.ρ.V, ∀ σ ∈ P.inertiaSubgroupIn ℚ,
        DQ.ρ.ρ σ (b 0) = ((χ (πΔ (cyc σ)) : DQ.Rˣ) : DQ.R) • b 0 ∧
        DQ.ρ.ρ σ (b 1) = (((χ (πΔ (cyc σ)))⁻¹ : DQ.Rˣ) : DQ.R) • b 1)
    (d : Multiplicative (ZMod (p ^ k))) :
    ε ((χ d : DQ.Rˣ) : DQ.R) = 1 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_DeformationRingData_algHom_inertiaCharacter_eq_one_of_forall_isUnramifiedAt.solution
