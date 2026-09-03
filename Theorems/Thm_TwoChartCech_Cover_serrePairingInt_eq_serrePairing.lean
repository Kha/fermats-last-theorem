import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import Definitions.Def_AlgebraicCurve_SerrePairing
import P2M.Util
import P2M.Sol.S_TwoChartCech_Cover_serrePairingInt_eq_serrePairing

set_option autoImplicit false

universe u w

theorem TwoChartCech.Cover.serrePairingInt_eq_serrePairing
    {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar k F]
    [∀ v : AlgebraicCurve.Place k F, v.DCoordGenerates] [Nontrivial Ω[F⁄k]]
    [AlgebraicCurve.HasCanonicalDivisor (K := k) (F := F)] [AlgebraicCurve.HasPrincipalDivisors k F]
    (hRT : AlgebraicCurve.ResidueTheorem k F)
    {S₀ S₁ : Set (AlgebraicCurve.Place k F)} (hcover : S₀ ∪ S₁ = Set.univ)
    (𝒰 : TwoChartCech.Cover.{u, u} k) {ι : Type w} [Fintype ι]
    (Λ : ι → 𝒰.LaurentChart) (hv : 𝒰.ResiduesVanishOnCoboundaries Λ)
    (ψ : 𝒰.A01 →ₐ[k] F)
    (hψ : ∀ s : 𝒰.A01, ψ s ∈ AlgebraicCurve.lSpaceOn (S₀ ∩ S₁) (0 : AlgebraicCurve.Divisor k F))
    (e1 : 𝒰.structureSheaf.H1 →ₗ[k] AlgebraicCurve.cechH1 S₀ S₁ (0 : AlgebraicCurve.Divisor k F))
    (he1 : ∀ s : 𝒰.A01, e1 (Submodule.Quotient.mk s) = Submodule.Quotient.mk ⟨ψ s, hψ s⟩)
    (eΩ : 𝒰.kaehler.H0 →ₗ[k] ↥(AlgebraicCurve.regularDifferentials k F))
    (p : ι ↪ AlgebraicCurve.Place k F) (hp : Set.range p = S₀ᶜ)
    (hres : ∀ (i : ι) (s : 𝒰.A01) (ω : 𝒰.kaehler.H0),
      (Λ i).residue (s • 𝒰.kaehler.r0 ω.val.1) =
        AlgebraicCurve.kaehlerResidueTerm ((eΩ ω : ↥(AlgebraicCurve.regularDifferentials k F)) : Ω[F⁄k])
          (AlgebraicCurve.diagonalHom k F (ψ s)) (p i))
    (ω : 𝒰.kaehler.H0) (x : 𝒰.structureSheaf.H1) :
    𝒰.serrePairingInt Λ hv ω x = AlgebraicCurve.serrePairing hRT hcover (eΩ ω) (e1 x) := by p2m_exact_reverting @_root_.P2MW.S_TwoChartCech_Cover_serrePairingInt_eq_serrePairing.solution
