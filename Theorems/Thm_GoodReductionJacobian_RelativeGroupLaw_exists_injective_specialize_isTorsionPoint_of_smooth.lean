import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import P2M.Util
import P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_specialize_isTorsionPoint_of_smooth

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped nonZeroDivisors

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.exists_injective_specialize_isTorsionPoint_of_smooth
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (n : ℕ) (hn : IsUnit (n : R))
    (R' : Type u) [CommRing R'] [IsDomain R'] [Algebra R R']
    (hsm : Smooth (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (L : Type u) [Field L] [Algebra R' L] [Algebra K L] [Algebra R L]
    [IsScalarTower R R' L] [IsScalarTower R K L]
    [IsLocalization (Algebra.algebraMapSubmonoid R' R⁰) L]
    (k' : Type u) [Field k'] [Algebra R k'] (ψ : R' →ₐ[R] k') :
    ∃ r : {z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L)))
              (pullback.snd g (specGenericFibreInclusion R K)) //
            (LB.genericFibre K).IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K L))) n z}
          → {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
            LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) n y},
      Function.Injective r ∧
      ∀ z, ∃ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R R'))) g,
        LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R R'))) n x ∧
        Spec.map (CommRingCat.ofHom (algebraMap R' L)) ≫ x.1 =
          z.1.1 ≫ pullback.fst g (specGenericFibreInclusion R K) ∧
        (r z).1.1 = Spec.map (CommRingCat.ofHom (ψ : R' →+* k')) ≫ x.1 := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_specialize_isTorsionPoint_of_smooth.solution
