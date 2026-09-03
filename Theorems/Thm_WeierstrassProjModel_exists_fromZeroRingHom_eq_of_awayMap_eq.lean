import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_exists_fromZeroRingHom_eq_of_awayMap_eq

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel
  HomogeneousLocalization HomogeneousIdealQuotientGrading

attribute [local instance] MvPolynomial.gradedAlgebra

theorem WeierstrassProjModel.exists_fromZeroRingHom_eq_of_awayMap_eq
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) :
    let 𝒜 := projModelGradingCR V
    let Y : ProjModelRingCR V := Ideal.Quotient.mk _ (MvPolynomial.X 1)
    let Z : ProjModelRingCR V := Ideal.Quotient.mk _ (MvPolynomial.X 2)
    let hY : Y ∈ 𝒜 1 :=
      mk_mem_quotGradingSubmodule _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R 1))
    let hZ : Z ∈ 𝒜 1 :=
      mk_mem_quotGradingSubmodule _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R 2))
    Function.Injective (fromZeroRingHom 𝒜 (Submonoid.powers Y)) ∧
    ∀ (a : Away 𝒜 Y) (b : Away 𝒜 Z),
      awayMap 𝒜 hZ (rfl : Y * Z = Y * Z) a = awayMap 𝒜 hY (mul_comm Y Z) b →
      ∃ r : 𝒜 0, fromZeroRingHom 𝒜 (Submonoid.powers Y) r = a ∧ fromZeroRingHom 𝒜 (Submonoid.powers Z) r = b := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_exists_fromZeroRingHom_eq_of_awayMap_eq.solution
