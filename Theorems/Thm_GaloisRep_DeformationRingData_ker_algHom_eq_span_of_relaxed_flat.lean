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
import P2M.Sol.S_GaloisRep_DeformationRingData_ker_algHom_eq_span_of_relaxed_flat
attribute [-instance] instIsScalarTowerTensorProduct_definitions
attribute [-simp] closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open IsLocalRing Polynomial
theorem GaloisRep.DeformationRingData.ker_algHom_eq_span_of_relaxed_flat
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    (p : ℕ) (Smin Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime ∧ q ∉ Smin) {ρbar : ResidualGaloisRep (ResidueField 𝒪)}
    (Dmin : GaloisRep.DeformationRingData 𝒪 ρbar (GaloisRep.minimalFlatCondition 𝒪 p Smin))
    (DQ : GaloisRep.DeformationRingData 𝒪 ρbar (fun _A _ _ _ ρ =>
        GaloisRep.flatCondition 𝒪 p (Smin ∪ Q) ρ ∧
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
      Ideal.span (Set.range fun g : (Π q : Q, Multiplicative (ZMod (p ^ k q))) => ι (MonoidAlgebra.of 𝒪 _ g) - 1) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_DeformationRingData_ker_algHom_eq_span_of_relaxed_flat.solution
