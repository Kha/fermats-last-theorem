import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_serrePairingInt_bijective_and_flip_bijective

universe u w

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.serrePairingInt_bijective_and_flip_bijective
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}} {ι : Type w} [Fintype ι]
    (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    {k : Type u} [Field k] [Algebra R k] (hπ : Function.Surjective (algebraMap R k))
    (Λ : ι → (𝒱.cover c).LaurentChart)
    (Λk : ι → ((𝒱.pullback c k).cover (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))).LaurentChart)
    (hΛ : ∀ i y, (Λk i).expand ((Scheme.TwoAffineOpenCover.HomOver.baseChange 𝒱 c k).map01 y) =
      ((Λ i).expand y).map (algebraMap R k))
    (hv : (𝒱.cover c).ResiduesVanishOnCoboundaries Λ)
    (hvk : ((𝒱.pullback c k).cover
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))).ResiduesVanishOnCoboundaries Λk)
    [Module.Free R (𝒱.kaehlerSections c).H0] [Module.Finite R (𝒱.kaehlerSections c).H0]
    [Module.Free R (𝒱.structureSheafSections c).H1] [Module.Finite R (𝒱.structureSheafSections c).H1]
    (eH0 : k ⊗[R] (𝒱.kaehlerSections c).H0 ≃ₗ[k]
      ((𝒱.pullback c k).kaehlerSections (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))).H0)
    (heH0 : ∀ ω, eH0 (1 ⊗ₜ[R] ω) = Scheme.TwoAffineOpenCover.kaehlerH0baseChangeMap 𝒱 c k ω)
    (eH1 : k ⊗[R] (𝒱.structureSheafSections c).H1 ≃ₗ[k]
      ((𝒱.pullback c k).structureSheafSections (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))).H1)
    (heH1 : ∀ x, eH1 (1 ⊗ₜ[R] x) = Scheme.TwoAffineOpenCover.H1baseChangeMap 𝒱 c k x)
    (hk : Function.Bijective (((𝒱.pullback c k).cover
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))).serrePairingInt Λk hvk) ∧
      Function.Bijective (((𝒱.pullback c k).cover
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))).serrePairingInt Λk hvk).flip) :
    Function.Bijective ((𝒱.cover c).serrePairingInt Λ hv) ∧
      Function.Bijective ((𝒱.cover c).serrePairingInt Λ hv).flip := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_serrePairingInt_bijective_and_flip_bijective.solution
