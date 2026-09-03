import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul
    {R : Type u} [CommRing R] {G T : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R g) (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t g) :
    ∃ σ : pullback t g ≅ pullback t g,
      σ.hom ≫ pullback.fst t g = pullback.fst t g ∧
      σ.hom ≫ pullback.snd t g =
        (L.mul (pullback.fst t g ≫ t) ⟨pullback.fst t g ≫ a.1, by rw [Category.assoc, a.2]⟩
          ⟨pullback.snd t g, pullback.condition.symm⟩).1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_iso_pullback_hom_fst_eq_and_hom_snd_eq_mul.solution
