import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_adjoin_div_tensorProduct_bijective_of_flat

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.adjoin_div_tensorProduct_bijective_of_flat
    {C : Type*} [CommRing C] (I : Ideal C) (a : C)
    (S : Type*) [CommRing S] [Algebra C S] [IsLocalization.Away a S]
    {C' : Type*} [CommRing C'] [Algebra C C'] [Module.Flat C C']
    (S' : Type*) [CommRing S'] [Algebra C' S'] [Algebra C S'] [IsScalarTower C C' S']
    [IsLocalization.Away (algebraMap C C' a) S'] (φ : S →ₐ[C] S') :
    let B : Subalgebra C S := Algebra.adjoin C {x : S | ∃ i ∈ I, x * algebraMap C S a = algebraMap C S i}
    let B' : Subalgebra C' S' :=
      Algebra.adjoin C' {x : S' | ∃ i ∈ I.map (algebraMap C C'), x * algebraMap C' S' (algebraMap C C' a) = algebraMap C' S' i}
    let θ : C' ⊗[C] ↥B →ₐ[C'] S' :=
      Algebra.TensorProduct.lift (Algebra.ofId C' S') (φ.comp B.val) (fun _ _ => Commute.all _ _)
    Function.Injective θ ∧ ∀ x : S', x ∈ Set.range θ ↔ x ∈ B' := by p2m_exact_reverting @_root_.P2MW.S_Algebra_adjoin_div_tensorProduct_bijective_of_flat.solution
