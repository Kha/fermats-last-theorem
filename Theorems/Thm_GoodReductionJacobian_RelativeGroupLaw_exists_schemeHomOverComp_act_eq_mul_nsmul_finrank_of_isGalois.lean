import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois
    (K : Type u) [Field K] {A : Scheme.{u}} (fA : A ⟶ Spec (CommRingCat.of K))
    [IsSeparated fA] [LocallyOfFiniteType fA]
    (LA : RelativeGroupLaw K fA) (hc : LA.IsCommutative)
    {V : Scheme.{u}} (g : V ⟶ Spec (CommRingCat.of K))
    (act : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)),
      SchemeHomOver t fA → SchemeHomOver t g → SchemeHomOver t g)
    (act_natural : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (t' : T' ⟶ Spec (CommRingCat.of K)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
      (a : SchemeHomOver t fA) (v : SchemeHomOver t g),
      GoodReductionJacobian.schemeHomOverComp ψ hψ (act t a v) =
        act t' (GoodReductionJacobian.schemeHomOverComp ψ hψ a)
          (GoodReductionJacobian.schemeHomOverComp ψ hψ v))
    (act_mul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (a b : SchemeHomOver t fA) (v : SchemeHomOver t g),
      act t (LA.mul t a b) v = act t a (act t b v))
    (act_torsor : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (v w : SchemeHomOver t g),
      ∃! a : SchemeHomOver t fA, act t a v = w)
    (K' : Type u) [Field K'] [Algebra K K'] [FiniteDimensional K K'] [IsGalois K K']
    (P : Spec (CommRingCat.of K') ⟶ V) (hP : P ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K K'))) :
    ∃ φ : SchemeHomOver g fA,
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (a : SchemeHomOver t fA)
        (v : SchemeHomOver t g),
        NeronModelInfra.schemeHomOverComp (act t a v) φ =
          LA.mul t (NeronModelInfra.schemeHomOverComp v φ) (LA.nsmul t (Module.finrank K K') a) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_act_eq_mul_nsmul_finrank_of_isGalois.solution
