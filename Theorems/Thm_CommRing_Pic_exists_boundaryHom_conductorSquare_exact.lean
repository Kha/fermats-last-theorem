import Mathlib
import P2M.Util
import P2M.Sol.S_CommRing_Pic_exists_boundaryHom_conductorSquare_exact

universe u v

theorem CommRing.Pic.exists_boundaryHom_conductorSquare_exact
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [FaithfulSMul A B]
    (𝔠 : Ideal B) (h𝔠 : ∀ b ∈ 𝔠, b ∈ Set.range (algebraMap A B)) :
    ∃ δ : (B ⧸ 𝔠)ˣ →* CommRing.Pic A,
      (∀ u : (B ⧸ 𝔠)ˣ, ∃ I : Submodule A B,
        (∀ x : B, x ∈ I ↔ ∃ a : A,
          (u : B ⧸ 𝔠) * Ideal.Quotient.mk 𝔠 x = Ideal.Quotient.mk 𝔠 (algebraMap A B a)) ∧
        Nonempty ((δ u : CommRing.Pic A) ≃ₗ[A] ↥I)) ∧
      (∀ u : (B ⧸ 𝔠)ˣ, δ u = 1 ↔
        ∃ (t : Bˣ) (a : (A ⧸ 𝔠.comap (algebraMap A B))ˣ),
          (u : B ⧸ 𝔠) =
            Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (a : A ⧸ 𝔠.comap (algebraMap A B)) *
              Ideal.Quotient.mk 𝔠 (t : B)) ∧
      (∀ P : CommRing.Pic A, (∃ u, δ u = P) ↔
        CommRing.Pic.mapAlgebra A B P = 1 ∧
          CommRing.Pic.mapAlgebra A (A ⧸ 𝔠.comap (algebraMap A B)) P = 1) ∧
      (∀ (t : Bˣ) (a : (A ⧸ 𝔠.comap (algebraMap A B))ˣ),
        Ideal.Quotient.mk 𝔠 (t : B) =
            Ideal.quotientMap 𝔠 (algebraMap A B) le_rfl (a : A ⧸ 𝔠.comap (algebraMap A B)) →
          ∃ s : Aˣ, algebraMap A B s = t) := by p2m_exact_reverting @_root_.P2MW.S_CommRing_Pic_exists_boundaryHom_conductorSquare_exact.solution
