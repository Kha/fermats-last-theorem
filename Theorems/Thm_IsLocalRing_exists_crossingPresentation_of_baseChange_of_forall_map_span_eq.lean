import Mathlib
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_crossingPresentation_of_baseChange_of_forall_map_span_eq

set_option autoImplicit false

open scoped TensorProduct

theorem IsLocalRing.exists_crossingPresentation_of_baseChange_of_forall_map_span_eq
    {W W' S : Type*} [CommRing W] [IsLocalRing W] [CommRing W'] [IsLocalRing W']
    [Algebra W W'] [Module.Finite W W'] [Module.Flat W W'] [FaithfulSMul W W'] [Algebra.Etale W W']
    {Γ : Type*} [Group Γ] [Fintype Γ] [MulSemiringAction Γ W'] [SMulCommClass Γ W W']
    (hinv : ∀ w' : W', (∀ γ : Γ, γ • w' = w') ↔ w' ∈ Set.range (algebraMap W W'))
    (hcard : Fintype.card Γ = Module.finrank W W')
    [CommRing S] [IsNoetherianRing S] [IsLocalRing S] [Algebra W S]
    [IsLocalRing (S ⊗[W] W')]
    (π : W) (m : ℕ)
    (hπ : IsSMulRegular (S ⊗[W] W') (algebraMap W (S ⊗[W] W') π))
    (x' y' : S ⊗[W] W') (u' : (S ⊗[W] W')ˣ)
    (hxy : x' * y' = algebraMap W (S ⊗[W] W') π ^ m * ↑u')
    (hmax : IsLocalRing.maximalIdeal (S ⊗[W] W') =
      Ideal.span {algebraMap W (S ⊗[W] W') π, x', y'})
    (hstabx : ∀ γ : Γ, Ideal.map (Algebra.TensorProduct.map (AlgHom.id S S)
        (MulSemiringAction.toAlgHom W W' γ)) (Ideal.span {x'}) = Ideal.span {x'})
    (hstaby : ∀ γ : Γ, Ideal.map (Algebra.TensorProduct.map (AlgHom.id S S)
        (MulSemiringAction.toAlgHom W W' γ)) (Ideal.span {y'}) = Ideal.span {y'}) :
    ∃ (x y : S) (u : Sˣ),
      x * y = algebraMap W S π ^ m * ↑u ∧
      IsLocalRing.maximalIdeal S = Ideal.span {algebraMap W S π, x, y} ∧
      Ideal.span {(x ⊗ₜ[W] (1 : W'))} = Ideal.span {x'} ∧
      Ideal.span {(y ⊗ₜ[W] (1 : W'))} = Ideal.span {y'} := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_crossingPresentation_of_baseChange_of_forall_map_span_eq.solution
