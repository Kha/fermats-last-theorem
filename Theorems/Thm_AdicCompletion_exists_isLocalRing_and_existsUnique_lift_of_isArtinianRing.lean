import Mathlib
import P2M.Util
import P2M.Sol.S_AdicCompletion_exists_isLocalRing_and_existsUnique_lift_of_isArtinianRing
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

open IsLocalRing

theorem AdicCompletion.exists_isLocalRing_and_existsUnique_lift_of_isArtinianRing
    (B : Type) [CommRing B] [IsNoetherianRing B] (𝔭 : Ideal B) [𝔭.IsMaximal] :
    ∃ (_ : IsLocalRing (AdicCompletion 𝔭 B)) (_ : IsNoetherianRing (AdicCompletion 𝔭 B))
      (_ : IsAdicComplete (maximalIdeal (AdicCompletion 𝔭 B)) (AdicCompletion 𝔭 B)),
      maximalIdeal (AdicCompletion 𝔭 B) = 𝔭.map (algebraMap B (AdicCompletion 𝔭 B)) ∧
      Function.Surjective ((residue (AdicCompletion 𝔭 B)).comp (algebraMap B (AdicCompletion 𝔭 B))) ∧
      RingHom.ker ((residue (AdicCompletion 𝔭 B)).comp (algebraMap B (AdicCompletion 𝔭 B))) = 𝔭 ∧
      ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] (φ : B →+* T),
        (∀ b ∈ 𝔭, φ b ∈ maximalIdeal T) →
        ∃! Φ : AdicCompletion 𝔭 B →+* T, IsLocalHom Φ ∧ Φ.comp (algebraMap B (AdicCompletion 𝔭 B)) = φ := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_exists_isLocalRing_and_existsUnique_lift_of_isArtinianRing.solution
