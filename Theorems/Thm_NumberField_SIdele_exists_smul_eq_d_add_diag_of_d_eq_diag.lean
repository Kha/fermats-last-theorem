import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import P2M.Util
import P2M.Sol.S_NumberField_SIdele_exists_smul_eq_d_add_diag_of_d_eq_diag

set_option autoImplicit false
open IsDedekindDomain NumberField CategoryTheory

theorem NumberField.SIdele.exists_smul_eq_d_add_diag_of_d_eq_diag
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (HeightOneSpectrum (𝓞 E)))
    (n : ℕ) (hn : Nat.card (K ≃ₐ[E] K) ∣ n)
    (f₁ : (Fin 3 → (K ≃ₐ[E] K)) → NumberField.SUnits.sUnitsRep E K S)
    (c : (Fin 2 → (K ≃ₐ[E] K)) → NumberField.SIdele.obj E K S)
    (hc : ((groupCohomology.inhomogeneousCochains (NumberField.SIdele.obj E K S)).d 2 3).hom c =
      fun g => (NumberField.SIdele.diag E K S).hom (f₁ g)) :
    ∃ (ω : (Fin 1 → (K ≃ₐ[E] K)) → NumberField.SIdele.obj E K S) (e : (Fin 2 → (K ≃ₐ[E] K)) → NumberField.SUnits.sUnitsRep E K S),
      (n : ℤ) • c = ((groupCohomology.inhomogeneousCochains (NumberField.SIdele.obj E K S)).d 1 2).hom ω + fun g => (NumberField.SIdele.diag E K S).hom (e g) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_SIdele_exists_smul_eq_d_add_diag_of_d_eq_diag.solution
