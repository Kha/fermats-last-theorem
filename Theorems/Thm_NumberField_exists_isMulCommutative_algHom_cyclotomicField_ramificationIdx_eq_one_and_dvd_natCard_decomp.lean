import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import P2M.Util
import P2M.Sol.S_NumberField_exists_isMulCommutative_algHom_cyclotomicField_ramificationIdx_eq_one_and_dvd_natCard_decomp
set_option autoImplicit false
set_option maxHeartbeats 200000
open NumberField IsDedekindDomain

theorem NumberField.exists_isMulCommutative_algHom_cyclotomicField_ramificationIdx_eq_one_and_dvd_natCard_decomp
    (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (n : ℕ) (hn : n ≠ 0) :
    ∃ (m : ℕ) (_ : NeZero m) (F' : Type) (_ : Field F') (_ : NumberField F') (_ : Algebra E F') (_ : IsGalois E F')
      (_ : IsMulCommutative (F' ≃ₐ[E] F')),

      ((m : ℕ) : 𝓞 E) ∉ v.asIdeal ∧ Nonempty (F' →ₐ[E] CyclotomicField m E) ∧

      (∀ w : HeightOneSpectrum (𝓞 F'), w.under (𝓞 E) = v →
        (w.under (𝓞 E)).asIdeal.ramificationIdx' w.asIdeal = 1 ∧ n ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E F' w)) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_isMulCommutative_algHom_cyclotomicField_ramificationIdx_eq_one_and_dvd_natCard_decomp.solution
