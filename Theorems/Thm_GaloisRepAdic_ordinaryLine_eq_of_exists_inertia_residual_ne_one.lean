import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_FLTPrelim_Ramification
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_ordinaryLine_eq_of_exists_inertia_residual_ne_one

set_option autoImplicit false
theorem GaloisRepAdic.ordinaryLine_eq_of_exists_inertia_residual_ne_one
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (L L' : Submodule A ρ.V)
    (hLb : ∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0)
    (hL'b : ∃ b : Module.Basis (Fin 2) A ρ.V, L' = A ∙ b 0)
    (hLI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L)
    (hL'I : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L')
    (hram : ∃ τ ∈ P.inertiaSubgroupIn ℚ, ρ.residual.ρ τ ≠ 1) :
    L = L' := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_ordinaryLine_eq_of_exists_inertia_residual_ne_one.solution
