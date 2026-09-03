import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_eq_and_nsmul_eq_of_henselianLocalRing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_schemeHomOverComp_eq_and_nsmul_eq_of_henselianLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (n : ℕ) (hn : IsUnit (n : R))
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (y₀ : SchemeHomOver
      (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R)))) f)
    (hy₀ : G.nsmul _ n y₀ =
      GoodReductionJacobian.schemeHomOverComp
        (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))))
        (Category.comp_id _) x) :
    ∃ y : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f,
      GoodReductionJacobian.schemeHomOverComp
          (Spec.map (CommRingCat.ofHom (algebraMap R (IsLocalRing.ResidueField R))))
          (Category.comp_id _) y = y₀ ∧
        G.nsmul _ n y = x := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_eq_and_nsmul_eq_of_henselianLocalRing.solution
