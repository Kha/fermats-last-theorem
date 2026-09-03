import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SplitTorus_isFinite_schemeKerStr_and_finrank_eq_of_iso_torusScheme

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SplitTorus

theorem AlgebraicGeometry.SplitTorus.isFinite_schemeKerStr_and_finrank_eq_of_iso_torusScheme
    {κ : Type u} [Field κ] (t : ℕ) {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of κ))
    (L : RelativeGroupLaw κ f)
    (e : torusScheme κ t ≅ X) (hef : e.hom ≫ f = torusStr κ t)
    (hen : ∀ n : ℕ, e.hom ≫ L.schemeNsmul n =
      Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainRingHom κ (n • AddMonoidHom.id (Fin t → ℤ)))) ≫ e.hom)
    (m : ℕ) (hm : 0 < m) :
    IsFinite (L.schemeKerStr m) ∧
    (∃ e' : L.schemeKer m ≅ muScheme κ t m, e'.hom ≫ muStr κ t m = L.schemeKerStr m) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom (L.schemeKerStr m) ⊤
     Module.finrank κ Γ(L.schemeKer m, ⊤) = m ^ t) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SplitTorus_isFinite_schemeKerStr_and_finrank_eq_of_iso_torusScheme.solution
