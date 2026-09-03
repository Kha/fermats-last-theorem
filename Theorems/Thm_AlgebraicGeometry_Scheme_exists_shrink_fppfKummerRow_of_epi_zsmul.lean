import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_exists_shrink_fppfKummerRow_of_epi_zsmul

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme~fppfKummerRow_of_epi_zsmul~fppfKummerRow_naturality~fppfCohomology_kernel_zsmul_eq_zero"

theorem AlgebraicGeometry.Scheme.exists_shrink_fppfKummerRow_of_epi_zsmul
    (G : Sheaf (smallFppfTopology specInt) Ab.{1}) (n : ℤ) (hn : Epi (n • 𝟙 G))
    [Small.{0} (fppfCohomology specInt G 0)] [Small.{0} (fppfCohomology specInt (kernel (n • 𝟙 G)) 1)] :
    ∃ (hS : (ShortComplex.mk (kernel.ι (n • 𝟙 G)) (n • 𝟙 G) (kernel.condition (n • 𝟙 G))).ShortExact)
      (δ₀ : Shrink.{0} (fppfCohomology specInt G 0) →+ Shrink.{0} (fppfCohomology specInt (kernel (n • 𝟙 G)) 1))
      (ι₁ : Shrink.{0} (fppfCohomology specInt (kernel (n • 𝟙 G)) 1) →+ fppfCohomology specInt G 1),

      (∀ x : fppfCohomology specInt G 0, δ₀ (equivShrink (fppfCohomology specInt G 0) x) =
        equivShrink (fppfCohomology specInt (kernel (n • 𝟙 G)) 1) ((FppfCohomologyLES.cohomologyδ hS 0 1 rfl : fppfCohomology specInt G 0 →+ fppfCohomology specInt (kernel (n • 𝟙 G)) 1) x)) ∧
      (∀ y : fppfCohomology specInt (kernel (n • 𝟙 G)) 1, ι₁ (equivShrink (fppfCohomology specInt (kernel (n • 𝟙 G)) 1) y) = fppfCohomologyMap specInt (kernel.ι (n • 𝟙 G)) 1 y) ∧

      δ₀.ker = (n • AddMonoidHom.id (Shrink.{0} (fppfCohomology specInt G 0))).range ∧
      Function.Exact δ₀ ι₁ ∧
      ι₁.range = AddMonoidHom.ker (n • AddMonoidHom.id (fppfCohomology specInt G 1)) ∧

      (∀ y : Shrink.{0} (fppfCohomology specInt (kernel (n • 𝟙 G)) 1), n • y = 0) ∧

      (∀ (R : Type) [CommRing R] (ρ : R →+* End G),
        ∃ (_ : Module R (Shrink.{0} (fppfCohomology specInt G 0))) (_ : Module R (Shrink.{0} (fppfCohomology specInt (kernel (n • 𝟙 G)) 1))),
          (∀ (r : R) (x : fppfCohomology specInt G 0), r • equivShrink (fppfCohomology specInt G 0) x = equivShrink (fppfCohomology specInt G 0) (fppfCohomologyMap specInt (ρ r) 0 x)) ∧
          (∀ (r : R), ∃ w : (n • 𝟙 G) ≫ ρ r = ρ r ≫ (n • 𝟙 G), ∀ (y : fppfCohomology specInt (kernel (n • 𝟙 G)) 1),
            r • equivShrink (fppfCohomology specInt (kernel (n • 𝟙 G)) 1) y =
              equivShrink (fppfCohomology specInt (kernel (n • 𝟙 G)) 1) (fppfCohomologyMap specInt (kernel.map (n • 𝟙 G) (n • 𝟙 G) (ρ r) (ρ r) w) 1 y)) ∧
          (∀ (r : R) (x : Shrink.{0} (fppfCohomology specInt G 0)), δ₀ (r • x) = r • δ₀ x) ∧
          (∀ (r : R) (y : Shrink.{0} (fppfCohomology specInt (kernel (n • 𝟙 G)) 1)), ι₁ (r • y) = fppfCohomologyMap specInt (ρ r) 1 (ι₁ y)) ∧
          (∀ (m : ℤ) (x : Shrink.{0} (fppfCohomology specInt G 0)), (m : R) • x = m • x) ∧
          (∀ (m : ℤ) (y : Shrink.{0} (fppfCohomology specInt (kernel (n • 𝟙 G)) 1)), (m : R) • y = m • y)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_exists_shrink_fppfKummerRow_of_epi_zsmul.solution
