import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isUnitFactorizableAboveOfType_biInvariant_rightConv_ne_zero_of_mem_archCutSubmodule

set_option autoImplicit false

p2m_open "NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm~exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule"

theorem AutomorphicForm.exists_isUnitFactorizableAboveOfType_biInvariant_rightConv_ne_zero_of_mem_archCutSubmodule
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ) (hne : ∃ g, φ g ≠ 0)
    (hlev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      φ (g * k) = φ g)
    (hφt : φ ∈ archCutSubmodule K tys) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ,
      IsFactorizableTestFn K f ∧ IsArchBiFinite K tys f ∧
      (∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ∀ x, f (k * x) = f x ∧ f (x * k) = f x) ∧
      (∃ S : Finset (HeightOneSpectrum (𝓞 K)), (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S) ∧
        IsUnitFactorizableAboveOfType K K tys (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) S f ∧
        ∀ z, f z ≠ 0 →
          (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
            finComponent (𝓞 K) K v (glFin (𝓞 K) K z) ∈ localIntegralSet K v) ∧
          ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K, z = z₁ * z₂ ∧
            z₂ ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧
            ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ xv : GL (Fin 2) (v.adicCompletion K),
              z₁ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * z₁) ∧
      ∃ g, rightConv K φ f g ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isUnitFactorizableAboveOfType_biInvariant_rightConv_ne_zero_of_mem_archCutSubmodule.solution
