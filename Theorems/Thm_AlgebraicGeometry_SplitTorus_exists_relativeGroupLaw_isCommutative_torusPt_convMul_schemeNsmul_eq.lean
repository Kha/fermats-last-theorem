import Mathlib
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SplitTorus_exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.SplitTorus

theorem AlgebraicGeometry.SplitTorus.exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq
    (S : Type u) [CommRing S] (d : ℕ) :
    ∃ L : RelativeGroupLaw S (torusStr S d),
      L.IsCommutative ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)),
        ∃ e : SchemeHomOver t (torusStr S d) ≃ (Fin d → Γ(T, ⊤)ˣ),
          (∀ (x : SchemeHomOver t (torusStr S d)) (i : Fin d),
            (e x i : Γ(T, ⊤)) =
              ((Scheme.ΓSpecIso (CommRingCat.of (torusCoord S d))).inv ≫ x.1.appTop).hom
                (AddMonoidAlgebra.single (Pi.single i 1) 1)) ∧
          (∀ x y : SchemeHomOver t (torusStr S d), e (L.mul t x y) = e x * e y)) ∧
      (∀ (S' : Type u) [CommRing S'] [Algebra S S'] (χ χ' : WithConv (torusCoord S d →ₐ[S] S')),
        torusPt S S' d (χ * χ').ofConv =
          L.mul _ (torusPt S S' d χ.ofConv) (torusPt S S' d χ'.ofConv)) ∧
      (∀ (S' : Type u) [CommRing S'] [Algebra S S'],
        torusPt S S' d (1 : WithConv (torusCoord S d →ₐ[S] S')).ofConv = L.one _) ∧
      (∀ n : ℕ, L.schemeNsmul n =
        Spec.map (CommRingCat.ofHom
          (AddMonoidAlgebra.mapDomainRingHom S (n • AddMonoidHom.id (Fin d → ℤ))))) ∧
      (∀ n : ℕ, 0 < n → IsFinite (L.schemeNsmul n) ∧ Flat (L.schemeNsmul n)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SplitTorus_exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq.solution
