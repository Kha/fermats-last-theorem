import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_H1_structureSheaf_of_isReduced_of_finrank_coker_fibre_const

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.free_H1_structureSheaf_of_isReduced_of_finrank_coker_fibre_const
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [_root_.IsReduced R]
    {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (hfin : Module.Finite R (𝒱.structureSheafSections c).H1) {n : ℕ}
    (hH1 : ∀ 𝔭 : PrimeSpectrum R, Module.finrank 𝔭.asIdeal.ResidueField
      ((𝔭.asIdeal.ResidueField ⊗[R] (𝒱.cover c).A01) ⧸
        LinearMap.range ((𝒱.structureSheafSections c).cechDiff.baseChange 𝔭.asIdeal.ResidueField)) = n) :
    Module.Free R (𝒱.structureSheafSections c).H1 ∧
      Module.finrank R (𝒱.structureSheafSections c).H1 = n ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        ∃ (e01 : (A ⊗[R] (𝒱.cover c).A01) ≃ₐ[A]
            ((𝒱.pullback c A).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).A01)
          (e : A ⊗[R] (𝒱.structureSheafSections c).H1 ≃ₗ[A]
            ((𝒱.pullback c A).structureSheafSections
              (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))).H1),
          (∀ s, e01 ((1 : A) ⊗ₜ[R] s)
              = ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)).app (𝒱.U0 ⊓ 𝒱.U1)).hom s) ∧
          ∀ (a : A) (y : (𝒱.cover c).A01),
            e (a ⊗ₜ[R] Submodule.Quotient.mk y) = Submodule.Quotient.mk (e01 (a ⊗ₜ[R] y)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_free_H1_structureSheaf_of_isReduced_of_finrank_coker_fibre_const.solution
