import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFrame
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalOmega_isAdicFrame_of_injective_of_forall_le_one_iff_mem_range

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.Omega

theorem CerednikDrinfeld.FormalOmega.isAdicFrame_of_injective_of_forall_le_one_iff_mem_range
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪]
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (C : Type) [Field C] [Algebra K₀ C] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
    (hrk : ∀ x y : C, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    [CompleteSpace C]
    (h𝒪 : ∀ x : K₀, x ∈ Set.range (algebraMap 𝒪 K₀) ↔ Valued.v (algebraMap K₀ C x) ≤ 1)
    (ϖ : Omega.PseudoUniformizer K₀ C) (hϖ : algebraMap 𝒪 K₀ π = ϖ.ϖ)
    (R : Type) [CommRing R] [Algebra 𝒪 R] [Algebra R C] [Algebra 𝒪 C] [IsScalarTower 𝒪 R C] [IsScalarTower 𝒪 K₀ C]
    (hinj : Function.Injective (algebraMap R C))
    (hrange : ∀ c : C, Valued.v c ≤ 1 ↔ c ∈ Set.range (algebraMap R C)) :
    IsAdicFrame π ϖ R := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalOmega_isAdicFrame_of_injective_of_forall_le_one_iff_mem_range.solution
