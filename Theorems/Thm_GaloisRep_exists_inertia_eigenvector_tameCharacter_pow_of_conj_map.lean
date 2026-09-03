import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_TameCharacter
import P2M.Util
import P2M.Sol.S_GaloisRep_exists_inertia_eigenvector_tameCharacter_pow_of_conj_map

set_option autoImplicit false

theorem GaloisRep.exists_inertia_eigenvector_tameCharacter_pow_of_conj_map
    (p : ℕ) [Fact p.Prime] {F F' : Type} [Field F] [Field F'] (e : F →+* F')
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F)
    (ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin 2) F')
    (g : GL (Fin 2) F') (hconj : ∀ σ, (ρ' σ).val = g.val * (ρ σ).val.map e * (g⁻¹).val)
    (kn : ℕ) (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (p ^ 2 - 1) = (p : AlgebraicClosure ℚ))
    (ψk' : F' →+* IsLocalRing.ResidueField P)
    (h' : ∃ v' : Fin 2 → IsLocalRing.ResidueField P, v' ≠ 0 ∧
      ((∀ σ ∈ P.inertiaSubgroupIn ℚ,
          ((ρ' σ).val.map ψk').mulVec v' = P.tameCharacter π σ ^ (kn - 1) • v') ∨
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          ((ρ' σ).val.map ψk').mulVec v' = (P.tameCharacter π σ ^ p) ^ (kn - 1) • v'))) :
    ∃ v : Fin 2 → IsLocalRing.ResidueField P, v ≠ 0 ∧
      ((∀ σ ∈ P.inertiaSubgroupIn ℚ,
          ((ρ σ).val.map (ψk'.comp e)).mulVec v = P.tameCharacter π σ ^ (kn - 1) • v) ∨
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          ((ρ σ).val.map (ψk'.comp e)).mulVec v = (P.tameCharacter π σ ^ p) ^ (kn - 1) • v)) := by p2m_exact_reverting @_root_.P2MW.S_GaloisRep_exists_inertia_eigenvector_tameCharacter_pow_of_conj_map.solution
