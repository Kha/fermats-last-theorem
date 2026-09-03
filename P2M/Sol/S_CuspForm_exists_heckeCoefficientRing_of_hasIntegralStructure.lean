import Definitions.Def_CuspForm_HeckeAlgebra
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_HeckeLocal
import Theorems.Thm_CuspForm_heckeLocal_finite_residueField
import Theorems.Thm_CuspForm_heckeLocal_residue_pi
import Theorems.Thm_CuspForm_heckeLocal_adjoin_range_pi
import Theorems.Thm_CuspForm_heckeLocal_exists_point
import Theorems.Thm_CuspForm_heckeLocal_residue_surjective
import P2M.Util
namespace P2MW.S_CuspForm_exists_heckeCoefficientRing_of_hasIntegralStructure

open CuspForm

theorem solution (N : ℕ) [NeZero N] (S : Finset ℕ)
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    (θ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* IsLocalRing.ResidueField 𝒪)
    (hint : CuspForm.HasIntegralStructure N 2) :
    ∃ (T : Type) (_ : CommRing T) (_ : IsLocalRing T) (_ : IsNoetherianRing T)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal T) T) (_ : Algebra 𝒪 T)
      (_ : IsLocalHom (algebraMap 𝒪 T)) (_ : Module.Finite 𝒪 T) (_ : Module.Free 𝒪 T),
      Finite (IsLocalRing.ResidueField T) ∧
      ∃ π : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* T,
        (∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ),
          IsLocalRing.residue T (π t) =
            IsLocalRing.ResidueField.map (algebraMap 𝒪 T) (θ t)) ∧
        Algebra.adjoin 𝒪 (Set.range π) = ⊤ ∧
        (∀ χ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* 𝒪,
          (∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ), IsLocalRing.residue 𝒪 (χ t) = θ t) →
            ∃ ψ : T →ₐ[𝒪] 𝒪, ∀ t : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ), ψ (π t) = χ t) ∧
        Function.Surjective (IsLocalRing.residue T ∘ algebraMap 𝒪 T) := by
  haveI : Fact (CuspForm.HasIntegralStructure N 2) := ⟨hint⟩
  exact ⟨heckeLocal N (↑S : Set ℕ) 𝒪 θ, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    heckeLocal.finite_residueField N _ 𝒪 θ,
    heckeLocal.π N _ 𝒪 θ, heckeLocal.residue_pi N _ 𝒪 θ, heckeLocal.adjoin_range_pi N _ 𝒪 θ hint,
    heckeLocal.exists_point N _ 𝒪 θ hint, heckeLocal.residue_surjective N _ 𝒪 θ⟩
