import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_comp_schemeNsmul_eq_of_comp_frobenius_eq_of_isCommutative

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.comp_schemeNsmul_eq_of_comp_frobenius_eq_of_isCommutative
    (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of (ZMod p))} [LocallyOfFiniteType f]
    (L : RelativeGroupLaw (ZMod p) f) (hc : L.IsCommutative)
    (F : SchemeHomOver f f)
    (hF : ∀ (B : Type) [CommRing B] [Algebra (ZMod p) B] [CharP B p]
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) B))) f),
      (NeronModelInfra.schemeHomOverComp x F).1 = Spec.map (CommRingCat.ofHom (frobenius B p)) ≫ x.1)
    {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ X) (h : g₁ ≫ F.1 = g₂ ≫ F.1) :
    g₁ ≫ L.schemeNsmul p = g₂ ≫ L.schemeNsmul p := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_comp_schemeNsmul_eq_of_comp_frobenius_eq_of_isCommutative.solution
