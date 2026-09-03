import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_of_forall_iff_isInStabilizer

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u v

theorem GoodReductionJacobian.RelativeGroupLaw.exists_iso_hom_comp_eq_of_forall_iff_isInStabilizer
    {R : Type u} [CommRing R] {A K : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (𝓛 : A.Modules) (ι : K ⟶ A) [Mono ι]
    (hK : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
      (∃ κ : T ⟶ K, κ ≫ ι = x.1) ↔ L.IsInStabilizer 𝓛 t x)
    (y₁ y₂ : Spec (CommRingCat.of R) ⟶ K) (h₁ : y₁ ≫ ι ≫ f = 𝟙 _) (h₂ : y₂ ≫ ι ≫ f = 𝟙 _) :
    ∃ τ : K ≅ K, τ.hom ≫ ι ≫ f = ι ≫ f ∧ y₁ ≫ τ.hom = y₂ := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_of_forall_iff_isInStabilizer.solution
