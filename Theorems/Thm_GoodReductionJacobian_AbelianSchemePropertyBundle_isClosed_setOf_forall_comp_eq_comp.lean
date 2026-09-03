import Mathlib
import Definitions.Def_JacJ1Iface
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_isClosed_setOf_forall_comp_eq_comp

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.isClosed_setOf_forall_comp_eq_comp
    {S : Type} [CommRing S] {A Y : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)}
    (hA : AbelianSchemePropertyBundle S f)
    (g : Y ⟶ Spec (CommRingCat.of S)) [IsSeparated g] (τ : A ⟶ Y) (hτ : τ ≫ g = f)
    (c : Spec (CommRingCat.of S) ⟶ Y) (hc : c ≫ g = 𝟙 _) :
    IsClosed {s : ↥(Spec (CommRingCat.of S)) |
      ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ A),
        f.base (x.base (IsLocalRing.closedPoint K)) = s → x ≫ τ = x ≫ f ≫ c} := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_isClosed_setOf_forall_comp_eq_comp.solution
