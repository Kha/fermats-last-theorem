import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_JacJ1Iface
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_schemeNsmul_comp_eq_of_forall_isTorsionPoint

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.existsUnique_schemeNsmul_comp_eq_of_forall_isTorsionPoint
    (S : Type) [CommRing S]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f)
    (hc : L.IsCommutative)
    (n : ℕ)
    [Flat (L.schemeNsmul n)] [Surjective (L.schemeNsmul n)] [QuasiCompact (L.schemeNsmul n)]
    {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of S)) (L' : RelativeGroupLaw S f')
    (F : A ⟶ A') (hF : F ≫ f' = f)
    (hFhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ F =
        (L'.mul t ⟨P.1 ≫ F, by rw [Category.assoc, hF]; exact P.2⟩
          ⟨Q.1 ≫ F, by rw [Category.assoc, hF]; exact Q.2⟩).1)
    (hFker : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      L.IsTorsionPoint t n P → P.1 ≫ F = (L'.one t).1) :
    ∃ w : A ⟶ A', (L.schemeNsmul n ≫ w = F) ∧
      (∀ w' : A ⟶ A', L.schemeNsmul n ≫ w' = F → w' = w) ∧
      ∃ hw : w ≫ f' = f,
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t f),
          (L.mul t P Q).1 ≫ w =
            (L'.mul t ⟨P.1 ≫ w, by rw [Category.assoc, hw]; exact P.2⟩
              ⟨Q.1 ≫ w, by rw [Category.assoc, hw]; exact Q.2⟩).1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_schemeNsmul_comp_eq_of_forall_isTorsionPoint.solution
