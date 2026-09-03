import Definitions.Def_NarrowRayClassGroup
import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import P2M.Util
import P2M.Sol.S_LT_HeckeChar_exists_heckeCharOfRayClassChar

theorem LT.HeckeChar.exists_heckeCharOfRayClassChar
    (K : Type) [Field K] [NumberField K]
    (𝔣 : Ideal (NumberField.RingOfIntegers K))
    (χ : Deep.NTSupply.NarrowRayClassGroup K 𝔣 →* ℂˣ) :
    ∃ η : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ →* ℂˣ,
      HeckeCharacter.IsFiniteOrderHeckeChar K η ∧
      HeckeCharacter.AdmitsModulus K η 𝔣 ∧
      AutomorphicForm.IsUnitaryChar (NumberField.RingOfIntegers K) K η ∧
      ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
        (hv : ¬ v.asIdeal ∣ 𝔣),
        η (AutomorphicForm.uniformizerIdele K v)
          = χ (Deep.NTSupply.primeClass K 𝔣 v hv) := by p2m_exact_reverting @_root_.P2MW.S_LT_HeckeChar_exists_heckeCharOfRayClassChar.solution
