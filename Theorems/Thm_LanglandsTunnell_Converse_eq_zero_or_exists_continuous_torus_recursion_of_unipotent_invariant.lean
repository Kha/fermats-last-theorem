import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_Converse_eq_zero_or_exists_continuous_torus_recursion_of_unipotent_invariant
attribute [-instance] NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center
attribute [-simp] LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv AutomorphicForm.classSq_apply AutomorphicForm.classRepEmbedding_one AutomorphicForm.finIdeleExponentAt_one AutomorphicForm.classRepFinIdele_one AutomorphicForm.productionPinsGeneralOf_D AutomorphicForm.productionPinsGeneral_D AutomorphicForm.productionPinsGeneralOf_μ AutomorphicForm.productionPinsGeneralOf_U AutomorphicForm.productionPinsCompact_ν AutomorphicForm.productionPinsCompact_U AutomorphicForm.productionPinsCompact_D AutomorphicForm.productionPinsCompact_nS AutomorphicForm.productionPinsCompact_gen AutomorphicForm.productionPinsCompact_Z AutomorphicForm.productionPinsCompact_mS AutomorphicForm.productionPinsCompact_μ AutomorphicForm.productionPins_nS AutomorphicForm.productionPins_mS AutomorphicForm.productionPins_ν AutomorphicForm.productionPins_Z AutomorphicForm.productionPins_U AutomorphicForm.productionPins_μ AutomorphicForm.productionPins_gen AutomorphicForm.productionPins_D AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one
attribute [-simp] AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one

set_option autoImplicit false
open IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.SmoothCusp

theorem LanglandsTunnell.Converse.eq_zero_or_exists_continuous_torus_recursion_of_unipotent_invariant
    (K : Type) [Field K] [NumberField K] (Pi : HeckeEigensystem K ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (N : Ideal (𝓞 K))
    (ϕ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous ϕ)
    (hunip : ∀ (x : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), ϕ (unipotentGL2 x * g) = ϕ g)
    (hborel : ∀ γ ∈ borelSubgroup K, ∀ g : AdelicGL2 (𝓞 K) K, ϕ (globalPoints (𝓞 K) K γ * g) = ϕ g)
    (hlevel : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      ϕ (g * u) = ϕ g)
    (heigen : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      IsHeckeCosetEigenfunctionAt K (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (heckeGen (𝓞 K) K v) v ϕ (Pi.a v))
    (hcentralEigen : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
      ϕ (centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) * g)
        = (HeckeEigensystem.cNorm v)⁻¹ * Pi.b v * ϕ g) :
    (∀ g : AdelicGL2 (𝓞 K) K, ϕ g = 0) ∨
      ∃ (S₁ : Finset (HeightOneSpectrum (𝓞 K))) (ψ : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ → ℂ),
        Continuous ψ ∧ ψ (1, 1) ≠ 0 ∧
        (∀ (γ₁ γ₂ : Kˣ) (t₁ t₂ : (AdeleRing (𝓞 K) K)ˣ),
          ψ (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) γ₁ * t₁,
              Units.map (algebraMap K (AdeleRing (𝓞 K) K)) γ₂ * t₂) = ψ (t₁, t₂)) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S₁ → ∀ t₁ t₂ : (AdeleRing (𝓞 K) K)ˣ,
          HeckeEigensystem.cNorm v * ψ (uniformizerIdele K v * t₁, t₂) + ψ (t₁, uniformizerIdele K v * t₂)
            = Pi.a v * ψ (t₁, t₂)) ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S₁ → ∀ t₁ t₂ : (AdeleRing (𝓞 K) K)ˣ,
          ψ (uniformizerIdele K v * t₁, uniformizerIdele K v * t₂)
            = (HeckeEigensystem.cNorm v)⁻¹ * Pi.b v * ψ (t₁, t₂)) := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_Converse_eq_zero_or_exists_continuous_torus_recursion_of_unipotent_invariant.solution
