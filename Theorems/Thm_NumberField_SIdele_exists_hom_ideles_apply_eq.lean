import Mathlib
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import P2M.Util
import P2M.Sol.S_NumberField_SIdele_exists_hom_ideles_apply_eq

set_option autoImplicit false
open IsDedekindDomain NumberField CategoryTheory

theorem NumberField.SIdele.exists_hom_ideles_apply_eq
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (HeightOneSpectrum (𝓞 E))) (D : M4aHerbrand.IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (Φ : NumberField.SIdele.obj E K S →+ Additive (AdeleRing (𝓞 K) K)ˣ)
    (hΦρ : ∀ (g : K ≃ₐ[E] K) (y : NumberField.SIdele.obj E K S),
      Φ ((NumberField.SIdele.obj E K S).ρ g y) = Additive.ofMul (D.unitsAct g (Additive.toMul (Φ y)))) :
    ∃ ΦR : NumberField.SIdele.obj E K S ⟶ Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ,
      ∀ y : NumberField.SIdele.obj E K S, ΦR.hom y = Φ y := by p2m_exact_reverting @_root_.P2MW.S_NumberField_SIdele_exists_hom_ideles_apply_eq.solution
