import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_isProper_isIntegral_forall_schemeHomOverComp_eq_foldr_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isProper_isIntegral_forall_schemeHomOverComp_eq_foldr_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : Scheme.{u}} {g : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k g)
    {n : ℕ} {C : Fin n → Scheme.{u}} (c : ∀ i : Fin n, C i ⟶ Spec (CommRingCat.of k))
    [∀ i : Fin n, IsProper (c i)] [∀ i : Fin n, IsIntegral (C i)]
    (ν : ∀ i : Fin n, SchemeHomOver (c i) g) :
    ∃ (X : Scheme.{u}) (x : X ⟶ Spec (CommRingCat.of k)) (_ : IsProper x) (_ : IsIntegral X)
      (V : SchemeHomOver x g),
      (∀ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) x,
        ∃ y : ∀ i : Fin n, SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (c i),
          NeronModelInfra.schemeHomOverComp P V =
            (List.ofFn fun i : Fin n => NeronModelInfra.schemeHomOverComp (y i) (ν i)).foldr
              (fun Q R => L.mul (𝟙 (Spec (CommRingCat.of k))) Q R) (L.one (𝟙 (Spec (CommRingCat.of k))))) ∧
      (∀ y : ∀ i : Fin n, SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (c i),
        ∃ P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) x,
          NeronModelInfra.schemeHomOverComp P V =
            (List.ofFn fun i : Fin n => NeronModelInfra.schemeHomOverComp (y i) (ν i)).foldr
              (fun Q R => L.mul (𝟙 (Spec (CommRingCat.of k))) Q R) (L.one (𝟙 (Spec (CommRingCat.of k))))) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isProper_isIntegral_forall_schemeHomOverComp_eq_foldr_of_isAlgClosed.solution
