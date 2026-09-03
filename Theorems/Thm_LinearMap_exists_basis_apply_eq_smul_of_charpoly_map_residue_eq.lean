import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_exists_basis_apply_eq_smul_of_charpoly_map_residue_eq

set_option autoImplicit false

universe u v
theorem LinearMap.exists_basis_apply_eq_smul_of_charpoly_map_residue_eq {R : Type u} [CommRing R] [IsLocalRing R] [HenselianLocalRing R]
    {V : Type v} [AddCommGroup V] [Module R V] (b₀ : Module.Basis (Fin 2) R V) (Φ : Module.End R V)
    {α β : IsLocalRing.ResidueField R} (hαβ : α ≠ β)
    (hchar : ((LinearMap.toMatrix b₀ b₀ Φ).charpoly).map (IsLocalRing.residue R)
      = (Polynomial.X - Polynomial.C α) * (Polynomial.X - Polynomial.C β)) :
    ∃ (b : Module.Basis (Fin 2) R V) (a d : R), IsUnit (a - d) ∧
      IsLocalRing.residue R a = α ∧ IsLocalRing.residue R d = β ∧
      Φ (b 0) = a • b 0 ∧ Φ (b 1) = d • b 1 := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_basis_apply_eq_smul_of_charpoly_map_residue_eq.solution
