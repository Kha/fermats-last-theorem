import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleBox
import P2M.Util
import P2M.Sol.S_NumberField_TateGlobal_apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous

set_option autoImplicit false

open NumberField NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdeleRing IsDedekindDomain

theorem NumberField.TateGlobal.apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous
    (F : Type) [Field F] [NumberField F] (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχ : Continuous χ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : ∀ v ∉ S, IsUnramifiedCharAt χ v) :
    ∀ u : (AdeleRing (𝓞 F) F)ˣ,
      (u : AdeleRing (𝓞 F) F).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 F) F).2 v = 1) →
      finitePartUnits (𝓞 F) F u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F →
      χ u = 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_TateGlobal_apply_eq_one_of_forall_isUnramifiedCharAt_of_continuous.solution
