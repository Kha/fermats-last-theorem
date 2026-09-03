import Mathlib
import P2M.Util
import P2M.Sol.S_AdicCompletion_exists_ringHom_ringEquiv_adjoinRoot_of_etale_of_isMaximal
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

universe u

theorem AdicCompletion.exists_ringHom_ringEquiv_adjoinRoot_of_etale_of_isMaximal
    {R₀ : Type u} [CommRing R₀] [IsNoetherianRing R₀]
    {B : Type u} [CommRing B] [Algebra R₀ B] [Algebra.Etale R₀ B]
    (P : Ideal R₀) [P.IsMaximal] (q : Ideal B) [q.IsMaximal] [q.LiesOver P]
    (α : B ⧸ q) (hα : Algebra.adjoin (R₀ ⧸ P) {α} = ⊤)
    (f : Polynomial (AdicCompletion P R₀)) (hf : f.Monic)
    (hfα : f.map ((algebraMap (R₀ ⧸ P) (B ⧸ q)).comp (AdicCompletion.evalOneₐ P).toRingHom) =
      (minpoly (R₀ ⧸ P) α).map (algebraMap (R₀ ⧸ P) (B ⧸ q))) :
    ∃ φ : AdicCompletion P R₀ →+* AdicCompletion q B,
      φ.comp (algebraMap R₀ (AdicCompletion P R₀)) = (algebraMap B (AdicCompletion q B)).comp (algebraMap R₀ B) ∧
      Ideal.map φ (P.map (algebraMap R₀ (AdicCompletion P R₀))) = q.map (algebraMap B (AdicCompletion q B)) ∧
      ∃ e : AdjoinRoot f ≃+* AdicCompletion q B,
        (∀ r : AdicCompletion P R₀, e (AdjoinRoot.of f r) = φ r) ∧
        ∃ b : B, Ideal.Quotient.mk q b = α ∧
          e (AdjoinRoot.root f) - algebraMap B (AdicCompletion q B) b ∈ q.map (algebraMap B (AdicCompletion q B)) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_exists_ringHom_ringEquiv_adjoinRoot_of_etale_of_isMaximal.solution
