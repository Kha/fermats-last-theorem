import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_kaehlerH0_of_isReduced_of_finrank_ker_fibre_const

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.free_kaehlerH0_of_isReduced_of_finrank_ker_fibre_const
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [_root_.IsReduced R]
    {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    [Module.Flat R Ω[(𝒱.cover c).A0⁄R]] [Module.Flat R Ω[(𝒱.cover c).A1⁄R]]
    [Module.Flat R Ω[(𝒱.cover c).A01⁄R]]
    (hfin : Module.Finite R (𝒱.kaehlerSections c).H0 ∧ Module.Finite R (𝒱.kaehlerSections c).H1) {n : ℕ}
    (hH0 : ∀ 𝔭 : PrimeSpectrum R, Module.finrank 𝔭.asIdeal.ResidueField
      (LinearMap.ker ((𝒱.kaehlerSections c).cechDiff.baseChange 𝔭.asIdeal.ResidueField)) = n) :
    Module.Free R (𝒱.kaehlerSections c).H0 ∧
      Module.finrank R (𝒱.kaehlerSections c).H0 = n ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerBaseChangeHom (𝒱.kaehlerSections c).cechDiff A) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_kaehlerH0_of_isReduced_of_finrank_ker_fibre_const.solution
