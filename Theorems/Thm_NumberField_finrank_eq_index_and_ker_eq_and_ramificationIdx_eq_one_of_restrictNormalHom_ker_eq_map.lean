import Mathlib
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import P2M.Util
import P2M.Sol.S_NumberField_finrank_eq_index_and_ker_eq_and_ramificationIdx_eq_one_of_restrictNormalHom_ker_eq_map

set_option autoImplicit false
open NumberField IsDedekindDomain M4aHerbrand

theorem NumberField.finrank_eq_index_and_ker_eq_and_ramificationIdx_eq_one_of_restrictNormalHom_ker_eq_map
    (E F F' : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field F'] [NumberField F']
    [Algebra E F] [Algebra E F'] [Algebra F F'] [IsScalarTower E F F'] [IsGalois E F'] [IsGalois E F]
    [IsMulCommutative (F' ≃ₐ[E] F')]
    (r' : (AdeleRing (𝓞 E) E)ˣ →* (F' ≃ₐ[E] F')) (hsurj : Function.Surjective r')
    (H₀ : Subgroup (AdeleRing (𝓞 E) E)ˣ) (hH₀ : r'.ker ≤ H₀)
    (hΓ : (AlgEquiv.restrictNormalHom F : (F' ≃ₐ[E] F') →* (F ≃ₐ[E] F)).ker = H₀.map r') :
    Module.finrank E F = H₀.index ∧
    (∀ rF : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F), Function.Surjective rF → H₀ ≤ rF.ker → rF.ker = H₀) ∧
    (∀ v : HeightOneSpectrum (𝓞 E),
      (∀ w' : HeightOneSpectrum (𝓞 F'), w'.asIdeal.under (𝓞 E) = v.asIdeal →
        w'.asIdeal.inertia (F' ≃ₐ[E] F') ≤ H₀.map r') →
      ∀ w : HeightOneSpectrum (𝓞 F), w.asIdeal.under (𝓞 E) = v.asIdeal →
        Ideal.ramificationIdx' (w.asIdeal.under (𝓞 E)) w.asIdeal = 1) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_finrank_eq_index_and_ker_eq_and_ramificationIdx_eq_one_of_restrictNormalHom_ker_eq_map.solution
