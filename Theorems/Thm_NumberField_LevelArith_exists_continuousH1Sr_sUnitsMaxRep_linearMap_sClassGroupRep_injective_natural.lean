import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_SUnitsMax
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural
attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField NumberField.LevelArith TensorProduct Pointwise

theorem NumberField.LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L] :
    ∃ f : ↥(continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) →ₗ[ℤ] (sClassGroupRep ↥L ↥L (S : Set Nat.Primes)),
      Function.Injective f ∧
        Submodule.map f (Submodule.torsionBy ℤ ↥(continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (p : ℤ)) =
          Submodule.torsionBy ℤ (sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) (p : ℤ) ∧
        ∀ (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (τ : ↥L ≃ₐ[ℚ] ↥L),
          (∀ y : ↥L, σ (y : AlgebraicClosure ℚ) = ((τ y : ↥L) : AlgebraicClosure ℚ)) →
          ∀ (c c' : ↥(levelCocyclesSr₁ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))),
            (∀ s s' : ↥L.fixingSubgroup, σ⁻¹ * (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = s' →
              sUnitsMaxRep.val S L ((c'.1 : ↥L.fixingSubgroup → (sUnitsMaxRep S L)) s) = σ • sUnitsMaxRep.val S L ((c.1 : ↥L.fixingSubgroup → (sUnitsMaxRep S L)) s')) →
            ∀ C : ClassGroup (𝓞 ↥L),
              f ⟨(H1π (sUnitsMaxRep S L)).hom c.1, H1π_mem_continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L) c.2⟩ =
                  Submodule.Quotient.mk (Additive.ofMul C) →
              f ⟨(H1π (sUnitsMaxRep S L)).hom c'.1, H1π_mem_continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L) c'.2⟩ =
                  Submodule.Quotient.mk (Additive.ofMul (τ • C)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective_natural.solution
