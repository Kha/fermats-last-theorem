import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_IsPushout_slice_ext_and_exists_of_flat

set_option autoImplicit false

open TensorProduct

universe u
theorem Algebra.IsPushout.slice_ext_and_exists_of_flat
    {B B₁ B' M N : Type u} [CommRing B] [CommRing B₁] [CommRing B'] [CommRing M] [CommRing N]
    [Algebra B B₁] [Algebra B' B₁] [Algebra B B'] [Algebra B M] [Algebra B' N] [Algebra M N] [Algebra B N]
    [IsScalarTower B B' N] [IsScalarTower B M N] [Algebra.IsPushout B B' M N] [Module.Flat B M]
    (hπ : Function.Surjective (algebraMap B B₁))
    (p : Fin 3 → (B' →ₐ[B] B))
    (hp : ∀ (i : Fin 3) (x : B'), algebraMap B B₁ (p i x) = algebraMap B' B₁ x)
    (hinj : ∀ x y : B', (∀ i, p i x = p i y) → x = y)
    (hsurj : ∀ b : Fin 3 → B, (∀ i j, algebraMap B B₁ (b i) = algebraMap B B₁ (b j)) → ∃ x : B', ∀ i, p i x = b i)
    (e : Fin 3 → (N →ₐ[B] M))
    (heM : ∀ (i : Fin 3) (m : M), e i (algebraMap M N m) = m)
    (heB : ∀ (i : Fin 3) (x : B'), e i (algebraMap B' N x) = algebraMap B M (p i x)) :
    (∀ n n' : N, (∀ i, e i n = e i n') → n = n') ∧
    (∀ m : Fin 3 → M, (∀ i j, m i - m j ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B M)) →
      ∃ n : N, ∀ i, e i n = m i) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsPushout_slice_ext_and_exists_of_flat.solution
