import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem AlgebraicGeometry.isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [QuasiCompact f]
    (L : RelativeGroupLaw k f) (hcomm : L.IsCommutative)
    (t : ℕ) (ι : Spec (CommRingCat.of (AddMonoidAlgebra k (Fin t → ℤ))) ⟶ X) [IsOpenImmersion ι] [IsClosedImmersion ι]
    (hιf : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k (Fin t → ℤ)))))
    (hιn : ∀ n : ℕ, ι ≫ L.schemeNsmul n =
      Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainRingHom k (n • AddMonoidHom.id (Fin t → ℤ)))) ≫ ι)
    (S : Finset (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f))
    (hidx : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, ∃ s ∈ S,
      ∃ τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k (Fin t → ℤ))))),
        x = L.mul (𝟙 _) s ⟨τ.1 ≫ ι, by rw [Category.assoc, hιf, τ.2]⟩)
    (m : ℕ) (hm : 0 < m) :
    IsFinite (L.schemeKerStr m) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom (L.schemeKerStr m) ⊤
     Module.finrank k Γ(L.schemeKer m, ⊤) ≤ S.card * m ^ t) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isFinite_schemeKerStr_and_finrank_le_of_isOpenImmersion_torus.solution
