import Mathlib
import Definitions.Def_AutomorphicForm_FormalBaseChange
import P2M.Util
namespace P2MW.S_AutomorphicForm_formalBaseChange_a_b_eq_of_under_eq

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open scoped BigOperators NumberField

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (π : HeckeEigensystem K ℂ) (w w' : HeightOneSpectrum (𝓞 L))
    (h : HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w') :
    ((formalBaseChange K L π).a w, (formalBaseChange K L π).b w) =
      ((formalBaseChange K L π).a w', (formalBaseChange K L π).b w') := by
  have h' : w.asIdeal.under (𝓞 K) = w'.asIdeal.under (𝓞 K) := congrArg HeightOneSpectrum.asIdeal h
  haveI : w.asIdeal.LiesOver (w'.asIdeal.under (𝓞 K)) := ⟨h'.symm⟩
  have hf : (w'.asIdeal.under (𝓞 K)).inertiaDeg' w.asIdeal = (w'.asIdeal.under (𝓞 K)).inertiaDeg' w'.asIdeal := by
    rw [Ideal.inertiaDeg'_eq_inertiaDeg, Ideal.inertiaDeg'_eq_inertiaDeg]
    exact Ideal.inertiaDeg_eq_of_isGaloisGroup (w'.asIdeal.under (𝓞 K)) w.asIdeal w'.asIdeal (L ≃ₐ[K] L)
  simp only [formalBaseChange_a, formalBaseChange_b, h]
  rw [show (HeightOneSpectrum.under (𝓞 K) w').asIdeal = w'.asIdeal.under (𝓞 K) from rfl, hf]

