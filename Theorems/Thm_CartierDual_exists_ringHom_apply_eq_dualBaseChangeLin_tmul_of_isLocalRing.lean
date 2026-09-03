import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CharacterClosure
import P2M.Util
import P2M.Sol.S_CartierDual_exists_ringHom_apply_eq_dualBaseChangeLin_tmul_of_isLocalRing

set_option autoImplicit false

universe u v w

open IsLocalRing
open scoped TensorProduct

theorem CartierDual.exists_ringHom_apply_eq_dualBaseChangeLin_tmul_of_isLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R]
    {B : Type v} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B] :
    ∃ r : CartierDual R B →+* CartierDual (ResidueField R) (ResidueField R ⊗[R] B),
      (∀ φ, r φ = CartierDual.dualBaseChangeLin R (ResidueField R) B ((1 : ResidueField R) ⊗ₜ[R] φ)) ∧
      Function.Surjective r ∧
      RingHom.ker r = (maximalIdeal R).map (algebraMap R (CartierDual R B)) := by p2m_exact_reverting @_root_.P2MW.S_CartierDual_exists_ringHom_apply_eq_dualBaseChangeLin_tmul_of_isLocalRing.solution
