import Mathlib
import P2M.Util
import P2M.Sol.S_Subalgebra_algebraMap_norm_eq_and_residue_norm_eq_mul

set_option autoImplicit false

open scoped nonZeroDivisors TensorProduct
theorem Subalgebra.algebraMap_norm_eq_and_residue_norm_eq_mul {V K F : Type*} [CommRing V] [IsDomain V]
    [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] [Field F] [Algebra K F]
    [Algebra V F] [IsScalarTower V K F] (S : Subalgebra V F) [Module.Finite V S]
    (hspan : Submodule.span K (S : Set F) = ⊤)
    {κ₁ κ₂ : Type*} [Field κ₁] [Field κ₂]
    [Algebra (IsLocalRing.ResidueField V) κ₁] [Algebra (IsLocalRing.ResidueField V) κ₂]
    [Algebra V κ₁] [Algebra V κ₂] [IsScalarTower V (IsLocalRing.ResidueField V) κ₁]
    [IsScalarTower V (IsLocalRing.ResidueField V) κ₂]
    [FiniteDimensional (IsLocalRing.ResidueField V) κ₁]
    [FiniteDimensional (IsLocalRing.ResidueField V) κ₂]
    (ρ₁ : S →ₐ[V] κ₁) (ρ₂ : S →ₐ[V] κ₂)
    (hsurj : Function.Surjective fun s : S => (ρ₁ s, ρ₂ s))
    (hdim : Module.finrank (IsLocalRing.ResidueField V) κ₁
      + Module.finrank (IsLocalRing.ResidueField V) κ₂ = Module.finrank K F) (s : S) :
    algebraMap V K (Algebra.norm V s) = Algebra.norm K (s : F) ∧
      IsLocalRing.residue V (Algebra.norm V s)
        = Algebra.norm (IsLocalRing.ResidueField V) (ρ₁ s)
            * Algebra.norm (IsLocalRing.ResidueField V) (ρ₂ s) := by p2m_exact_reverting @_root_.P2MW.S_Subalgebra_algebraMap_norm_eq_and_residue_norm_eq_mul.solution
