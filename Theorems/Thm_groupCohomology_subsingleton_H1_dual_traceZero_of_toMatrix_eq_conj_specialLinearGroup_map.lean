import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_subsingleton_H1_dual_traceZero_of_toMatrix_eq_conj_specialLinearGroup_map

set_option autoImplicit false

open Matrix MatrixGroups groupCohomology

theorem groupCohomology.subsingleton_H1_dual_traceZero_of_toMatrix_eq_conj_specialLinearGroup_map
    {k : Type} [Field k] [Finite k] [CharP k 3] (F : Subfield k)
    {V : Type} [AddCommGroup V] [Module k V] (b : Module.Basis (Fin 2) k V)
    (g : GL (Fin 2) k)
    {S : Type} [Group S] (σ : S →* Module.End k V) (hσ : Function.Injective σ)
    (hσS : ∀ s : S, ∃ m : SL(2, F), LinearMap.toMatrix b b (σ s) =
      (g : Matrix (Fin 2) (Fin 2) k) *
        (Matrix.SpecialLinearGroup.map F.subtype m : Matrix (Fin 2) (Fin 2) k) *
          ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k))
    (hSσ : ∀ m : SL(2, F), ∃ s : S, LinearMap.toMatrix b b (σ s) =
      (g : Matrix (Fin 2) (Fin 2) k) *
        (Matrix.SpecialLinearGroup.map F.subtype m : Matrix (Fin 2) (Fin 2) k) *
          ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k))
    [Module (ZMod 3) (LinearMap.ker (LinearMap.trace k V))]
    (A : Rep (ZMod 3) S)
    (e : A ≃ₗ[ZMod 3] Module.Dual (ZMod 3) (LinearMap.ker (LinearMap.trace k V)))
    (he : ∀ (s : S) (a : A) (X Y : LinearMap.ker (LinearMap.trace k V)),
      (Y : Module.End k V) = σ s⁻¹ * X * σ s → e (A.ρ s a) X = e a Y) :
    Subsingleton (H1 A) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_subsingleton_H1_dual_traceZero_of_toMatrix_eq_conj_specialLinearGroup_map.solution
