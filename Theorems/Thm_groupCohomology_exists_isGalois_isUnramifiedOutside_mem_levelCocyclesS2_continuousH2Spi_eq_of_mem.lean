import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_isGalois_isUnramifiedOutside_mem_levelCocyclesS2_continuousH2Spi_eq_of_mem
attribute [-instance] WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.exists_isGalois_isUnramifiedOutside_mem_levelCocyclesS2_continuousH2Spi_eq_of_mem
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (c : continuousH2S S (ofChar (k := ZMod p) (cycloChar p))) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ ↥F) (_ : IsGalois ℚ ↥F)
      (_ : F.IsUnramifiedOutside S) (_ : ζ ∈ F)
      (_ : ∀ q : ↥S, ∃ r ∈ F, r ^ p = (((q : Nat.Primes) : ℕ) : AlgebraicClosure ℚ))
      (f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ZMod p)
      (hf : f ∈ levelCocyclesS₂ S (ofChar (k := ZMod p) (cycloChar p))),
      continuousH2Sπ S (ofChar (k := ZMod p) (cycloChar p)) ⟨f, hf⟩ = c ∧
      ∀ (g g' s s' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        s ∈ F.fixingSubgroup → s' ∈ F.fixingSubgroup → f (g * s, g' * s') = f (g, g') := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_isGalois_isUnramifiedOutside_mem_levelCocyclesS2_continuousH2Spi_eq_of_mem.solution
