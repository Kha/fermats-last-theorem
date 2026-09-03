import Mathlib
import P2M.Util
import P2M.Sol.S_IntermediateField_finrank_adjoin_range_le_finrank_of_transcendental
set_option autoImplicit false

open scoped Polynomial

universe u

theorem IntermediateField.finrank_adjoin_range_le_finrank_of_transcendental
    (𝔽 : Type u) [Field 𝔽] (k : Type u) [Field k] [Algebra 𝔽 k]
    (κ : Type u) [Field κ] [Algebra 𝔽 κ] [Algebra 𝔽[X] κ] [IsScalarTower 𝔽 𝔽[X] κ]
    (hfin : FiniteDimensional ↥(IntermediateField.adjoin 𝔽 ({algebraMap 𝔽[X] κ Polynomial.X} : Set κ)) κ)
    (Ω : Type u) [Field Ω] [Algebra k Ω] [Algebra 𝔽 Ω] [IsScalarTower 𝔽 k Ω]
    (ρ : κ →ₐ[𝔽] Ω) (htr : Transcendental k (ρ (algebraMap 𝔽[X] κ Polynomial.X))) :
    Module.finrank ↥(IntermediateField.adjoin k ({⟨ρ (algebraMap 𝔽[X] κ Polynomial.X),
          IntermediateField.subset_adjoin k (Set.range ρ) ⟨_, rfl⟩⟩} : Set ↥(IntermediateField.adjoin k (Set.range ρ))))
        ↥(IntermediateField.adjoin k (Set.range ρ)) ≤
      Module.finrank ↥(IntermediateField.adjoin 𝔽 ({algebraMap 𝔽[X] κ Polynomial.X} : Set κ)) κ := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_finrank_adjoin_range_le_finrank_of_transcendental.solution
