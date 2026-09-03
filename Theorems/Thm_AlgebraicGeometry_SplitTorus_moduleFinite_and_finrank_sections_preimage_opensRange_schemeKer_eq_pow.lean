import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SplitTorus_moduleFinite_and_finrank_sections_preimage_opensRange_schemeKer_eq_pow

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian AlgebraicGeometry.SplitTorus

theorem AlgebraicGeometry.SplitTorus.moduleFinite_and_finrank_sections_preimage_opensRange_schemeKer_eq_pow
    {κ : Type u} [Field κ] (t : ℕ) {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of κ))
    (L : RelativeGroupLaw κ f)
    (ι : torusScheme κ t ⟶ X) [IsOpenImmersion ι] (hιf : ι ≫ f = torusStr κ t)
    (hιn : ∀ n : ℕ, ι ≫ L.schemeNsmul n =
      Spec.map (CommRingCat.ofHom
        (AddMonoidAlgebra.mapDomainRingHom κ (n • AddMonoidHom.id (Fin t → ℤ)))) ≫ ι)
    (m : ℕ) (hm : 0 < m) :
    letI V : (L.schemeKer m).Opens :=
      (pullback.fst (L.schemeNsmul m) (L.one (𝟙 (Spec (CommRingCat.of κ)))).1) ⁻¹ᵁ (Scheme.Hom.opensRange ι)
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (L.schemeKerStr m) V
    Module.Finite κ Γ(L.schemeKer m, V) ∧ Module.finrank κ Γ(L.schemeKer m, V) = m ^ t := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SplitTorus_moduleFinite_and_finrank_sections_preimage_opensRange_schemeKer_eq_pow.solution
