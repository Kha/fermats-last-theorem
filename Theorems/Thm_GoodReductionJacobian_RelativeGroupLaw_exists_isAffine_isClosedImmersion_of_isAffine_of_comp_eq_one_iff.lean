import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_isAffine_isClosedImmersion_of_isAffine_of_comp_eq_one_iff

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_isAffine_isClosedImmersion_of_isAffine_of_comp_eq_one_iff
    (k : Type u) [Field k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f)
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] [IsAffine N] [GeometricallyConnected (i ≫ f)]
    {Q : Scheme.{u}} (fQ : Q ⟶ Spec (CommRingCat.of k)) (LQ : RelativeGroupLaw k fQ)
    (q : SchemeHomOver f fQ) (h : ℕ) [SmoothOfRelativeDimension h q.1] [Surjective q.1]
    [QuasiCompact q.1]
    (hq : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) q =
        LQ.mul t (NeronModelInfra.schemeHomOverComp x q) (NeronModelInfra.schemeHomOverComp y q))
    (hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp x q = LQ.one t ↔
        ∃ y : SchemeHomOver t (i ≫ f),
          NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) = x)
    {M : Scheme.{u}} (j : M ⟶ Q) [IsClosedImmersion j] [IsAffine M] [ConnectedSpace M]
    (LM : RelativeGroupLaw k (j ≫ fQ)) (m : ℕ) [SmoothOfRelativeDimension m (j ≫ fQ)]
    (hj : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (j ≫ fQ)),
      NeronModelInfra.schemeHomOverComp (LM.mul t x y) (⟨j, rfl⟩ : SchemeHomOver (j ≫ fQ) fQ) =
        LQ.mul t (NeronModelInfra.schemeHomOverComp x (⟨j, rfl⟩ : SchemeHomOver (j ≫ fQ) fQ))
          (NeronModelInfra.schemeHomOverComp y (⟨j, rfl⟩ : SchemeHomOver (j ≫ fQ) fQ))) :
    ∃ (P : Scheme.{u}) (ι : P ⟶ G) (LP : RelativeGroupLaw k (ι ≫ f)),
      IsClosedImmersion ι ∧ IsAffine P ∧ ConnectedSpace P ∧
      SmoothOfRelativeDimension (h + m) (ι ≫ f) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (ι ≫ f)),
        NeronModelInfra.schemeHomOverComp (LP.mul t x y) (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ f) f))) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
        (∃ y : SchemeHomOver t (ι ≫ f),
            NeronModelInfra.schemeHomOverComp y (⟨ι, rfl⟩ : SchemeHomOver (ι ≫ f) f) = x) ↔
          ∃ z : SchemeHomOver t (j ≫ fQ),
            NeronModelInfra.schemeHomOverComp z (⟨j, rfl⟩ : SchemeHomOver (j ≫ fQ) fQ) =
              NeronModelInfra.schemeHomOverComp x q) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isAffine_isClosedImmersion_of_isAffine_of_comp_eq_one_iff.solution
