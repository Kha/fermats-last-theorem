import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import P2M.Util
import P2M.Sol.S_Deformation_DieudonneModule_exists_ringHom_addMonoidEnd_apply_eq_map

set_option autoImplicit false
open scoped TensorProduct in

theorem Deformation.DieudonneModule.exists_ringHom_addMonoidEnd_apply_eq_map
    (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime]
    {A : Type} [CommRing A] [Bialgebra R A]
    {κ : Type} [CommRing κ] (θ : κ → (A →ₐc[R] A))
    (hone : θ 1 = BialgHom.id R A)
    (hmul : ∀ a b : κ, θ (a * b) = (θ a).comp (θ b))
    (hadd : ∀ a b : κ, (θ (a + b) : A →ₐ[R] A).toLinearMap =
      LinearMap.mul' R A ∘ₗ TensorProduct.map (θ a : A →ₐ[R] A).toLinearMap (θ b : A →ₐ[R] A).toLinearMap ∘ₗ
        Coalgebra.comul (R := R) (A := A)) :
    ∃ Θ : κ →+* AddMonoid.End (Deformation.DieudonneModule R p A),
      ∀ (a : κ) (x : Deformation.DieudonneModule R p A),
        Θ a x = Deformation.DieudonneModule.map R p (θ a) x := by p2m_exact_reverting @_root_.P2MW.S_Deformation_DieudonneModule_exists_ringHom_addMonoidEnd_apply_eq_map.solution
