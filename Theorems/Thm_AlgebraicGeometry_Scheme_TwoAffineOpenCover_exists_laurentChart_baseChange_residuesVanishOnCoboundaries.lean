import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_baseChange_residuesVanishOnCoboundaries

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem exists_laurentChart_baseChange_residuesVanishOnCoboundaries
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A]
    {ιT : Type w} [Fintype ιT] (Λ : ιT → (𝒱.cover c).LaurentChart)
    (hv : (𝒱.cover c).ResiduesVanishOnCoboundaries Λ) :
    ∃ (ΛA : ιT → ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).LaurentChart)
      (_ : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).ResiduesVanishOnCoboundaries ΛA),
      ∀ i y, (ΛA i).expand ((HomOver.baseChange 𝒱 c A).map01 y) = ((Λ i).expand y).map (algebraMap R A) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_laurentChart_baseChange_residuesVanishOnCoboundaries.solution

end AlgebraicGeometry.Scheme.TwoAffineOpenCover
