import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic
import P2M.Util
import P2M.Sol.S_Submodule_exists_injective_linearMap_baseChange_torsionBySet_range_eq_eigenspace

set_option autoImplicit false

open scoped TensorProduct in

theorem Submodule.exists_injective_linearMap_baseChange_torsionBySet_range_eq_eigenspace
    {A : Type*} [CommRing A] {J : Type*} [AddCommGroup J] [Module A J]
    {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (I 𝔪 : Ideal A) [𝔪.IsMaximal] (hI : I ≤ 𝔪) (hp : (p : A) ∈ I)
    (hfin : Finite ↥(Submodule.torsionBySet A J (I : Set A)))
    (ι : A ⧸ 𝔪 →+* k) :
    letI := ι.toAlgebra
    ∃ j : k ⊗[A ⧸ 𝔪] ↥(Submodule.torsionBySet A J (𝔪 : Set A)) →ₗ[k]
        k ⊗[ℤ] ↥(Submodule.torsionBySet A J (I : Set A)),
      Function.Injective j ∧
      ∀ w : k ⊗[ℤ] ↥(Submodule.torsionBySet A J (I : Set A)),
        w ∈ LinearMap.range j ↔
          ∀ a : A,
            ((DistribSMul.toLinearMap ℤ ↥(Submodule.torsionBySet A J (I : Set A)) a).baseChange k) w =
              ι (Ideal.Quotient.mk 𝔪 a) • w := by p2m_exact_reverting @_root_.P2MW.S_Submodule_exists_injective_linearMap_baseChange_torsionBySet_range_eq_eigenspace.solution
