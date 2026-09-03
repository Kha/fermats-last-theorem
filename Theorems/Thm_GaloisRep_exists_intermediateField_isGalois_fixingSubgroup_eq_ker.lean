import Mathlib
import P2M.Util
import P2M.Sol.S_GaloisRep_exists_intermediateField_isGalois_fixingSubgroup_eq_ker

theorem GaloisRep.exists_intermediateField_isGalois_fixingSubgroup_eq_ker
    {G : Type*} [Group G] [Finite G] (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* G)
    (M : IntermediateField ℚ (AlgebraicClosure ℚ)) (hM : FiniteDimensional ℚ M)
    (hker : M.fixingSubgroup ≤ ρ.ker) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧
      F.fixingSubgroup = ρ.ker ∧ Module.finrank ℚ F ∣ Nat.card G := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_exists_intermediateField_isGalois_fixingSubgroup_eq_ker.solution
