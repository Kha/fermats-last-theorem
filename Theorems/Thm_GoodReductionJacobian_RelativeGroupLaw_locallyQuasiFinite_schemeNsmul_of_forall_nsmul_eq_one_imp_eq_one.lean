import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_forall_nsmul_eq_one_imp_eq_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_schemeNsmul_of_forall_nsmul_eq_one_imp_eq_one
    {k : Type u} [Field k] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType f]
    (G : RelativeGroupLaw k f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ)
    (hinj : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k K))) f),
      G.nsmul _ n x = G.one _ → x = G.one _) :
    LocallyQuasiFinite (G.schemeNsmul n) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_forall_nsmul_eq_one_imp_eq_one.solution
