import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isOpenImmersion_of_isClosedImmersion_of_isReduced_of_finite_index

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.isOpenImmersion_of_isClosedImmersion_of_isReduced_of_finite_index
    {k : Type u} [Field k] [IsAlgClosed k] {X T : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [IsReduced X]
    (L : RelativeGroupLaw k f)
    (tT : T ⟶ Spec (CommRingCat.of k)) (ι : T ⟶ X) [IsClosedImmersion ι] (hιf : ι ≫ f = tT)
    (hmul : ∀ τ τ' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) tT,
      ∃ τ'' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) tT,
        L.mul (𝟙 _) ⟨τ.1 ≫ ι, by rw [Category.assoc, hιf, τ.2]⟩ ⟨τ'.1 ≫ ι, by rw [Category.assoc, hιf, τ'.2]⟩ =
          ⟨τ''.1 ≫ ι, by rw [Category.assoc, hιf, τ''.2]⟩)
    (hinv : ∀ τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) tT,
      ∃ τ' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) tT,
        L.inv (𝟙 _) ⟨τ.1 ≫ ι, by rw [Category.assoc, hιf, τ.2]⟩ = ⟨τ'.1 ≫ ι, by rw [Category.assoc, hιf, τ'.2]⟩)
    (S : Finset (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f))
    (hidx : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, ∃ s ∈ S,
      ∃ τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) tT,
        x = L.mul (𝟙 _) s ⟨τ.1 ≫ ι, by rw [Category.assoc, hιf, τ.2]⟩) :
    IsOpenImmersion ι := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isOpenImmersion_of_isClosedImmersion_of_isReduced_of_finite_index.solution
