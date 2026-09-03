import Definitions.Def_NumberField_AdelicLevel
import P2M.Util
import P2M.Sol.S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat

theorem NumberField.AdelicLevel.finiteIdeleClassNumberOne_rat
    (δ : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ) :
    ∃ α : ℚˣ,
      (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
        (algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)
              ((α⁻¹ : ℚˣ) : ℚ)
            * (δ : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) v
          ∈ v.adicCompletionIntegers ℚ) ∧
      (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
        (algebraMap ℚ (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)
              ((α : ℚˣ) : ℚ)
            * ((δ⁻¹ : (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ) :
                IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) v
          ∈ v.adicCompletionIntegers ℚ) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat.solution
