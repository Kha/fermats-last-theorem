import Mathlib
import Definitions.Def_GaloisRep_FrobeniusPowerDense
import P2M.Util
import P2M.Sol.S_FrobeniusDensity_frobeniusPowerDense_of_le_ker
attribute [-instance] FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow AlgebraicClosure.Rat.isGalois
attribute [-simp] TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec

theorem FrobeniusDensity.frobeniusPowerDense_of_le_ker (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    [Algebra F (AlgebraicClosure ℚ)] [IsScalarTower ℚ F (AlgebraicClosure ℚ)]
    {H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    (hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ H)
    (S : Finset ℕ) : FrobeniusPowerDense S H := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_frobeniusPowerDense_of_le_ker.solution
