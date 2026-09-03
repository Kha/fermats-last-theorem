import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import P2M.Util
import P2M.Sol.S_AutomorphicForm_exists_isUnitFactorizableAboveOfType_principalLevel_tendsto_rightConv_of_mem_archCutSubmodule

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem AutomorphicForm.exists_isUnitFactorizableAboveOfType_principalLevel_tendsto_rightConv_of_mem_archCutSubmodule
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (tys : ArchTypeFamily L) (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f)
    (hlev : ∀ g : AdelicGL2 (𝓞 L) L,
      ∀ k ∈ principalLevel (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L,
        f (g * k) = f g)
    (harch : f ∈ archCutSubmodule L tys) :
    ∃ φ : ℕ → (AdelicGL2 (𝓞 L) L → ℂ),
      (∀ n, IsUnitFactorizableAboveOfType K L tys
        (principalLevel (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK (φ n)) ∧
      ∀ g, Filter.Tendsto (fun n => rightConv L f (φ n) g) Filter.atTop (nhds (f g)) := by p2m_exact_reverting @_root_.P2MW.S_AutomorphicForm_exists_isUnitFactorizableAboveOfType_principalLevel_tendsto_rightConv_of_mem_archCutSubmodule.solution
