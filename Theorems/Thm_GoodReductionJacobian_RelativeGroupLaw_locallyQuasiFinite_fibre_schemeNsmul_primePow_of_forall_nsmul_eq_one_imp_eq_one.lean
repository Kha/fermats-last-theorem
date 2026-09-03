import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawFibre
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_fibre_schemeNsmul_primePow_of_forall_nsmul_eq_one_imp_eq_one

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_fibre_schemeNsmul_primePow_of_forall_nsmul_eq_one_imp_eq_one
    (p : ℕ) [Fact p.Prime] {G : Scheme.{0}} {g : G ⟶ Spec (CommRingCat.of ℤ)} [LocallyOfFiniteType g]
    (L : RelativeGroupLaw ℤ g)
    (hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℤ)) (x y : SchemeHomOver t g),
      L.mul t x y = L.mul t y x)
    (htors : ∀ (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (k : ℕ)
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))) g),
      L.nsmul _ (p ^ k) x = L.one _ → x = L.one _) :
    ∀ s : Spec (CommRingCat.of ℤ), s.asIdeal = Ideal.span {(p : ℤ)} → ∀ k : ℕ, 0 < k →
      LocallyQuasiFinite ((L.fibre s).schemeNsmul (p ^ k)) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_fibre_schemeNsmul_primePow_of_forall_nsmul_eq_one_imp_eq_one.solution
