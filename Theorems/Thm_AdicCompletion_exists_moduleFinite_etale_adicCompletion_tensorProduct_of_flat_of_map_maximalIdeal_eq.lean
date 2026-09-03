import Mathlib
import P2M.Util
import P2M.Sol.S_AdicCompletion_exists_moduleFinite_etale_adicCompletion_tensorProduct_of_flat_of_map_maximalIdeal_eq
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem AdicCompletion.exists_moduleFinite_etale_adicCompletion_tensorProduct_of_flat_of_map_maximalIdeal_eq
    (V : Type) [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (D : Type) [CommRing D] [IsLocalRing D] [Algebra V D] [IsLocalHom (algebraMap V D)] [Module.Flat V D]
    (hVD : (maximalIdeal V).map (algebraMap V D) = maximalIdeal D)
    [Module.Finite (ResidueField V) (ResidueField D)] [Algebra.IsSeparable (ResidueField V) (ResidueField D)]
    (C : Type) [CommRing C] [Algebra V C] [IsNoetherianRing C]
    (𝔫 : Ideal C) [𝔫.IsMaximal] (h𝔫 : (maximalIdeal V).map (algebraMap V C) ≤ 𝔫)
    [IsNoetherianRing (C ⊗[V] D)]
    (x : Ideal (C ⊗[V] D)) [x.IsMaximal]
    (hx : 𝔫.map (algebraMap C (C ⊗[V] D)) ≤ x) :
    ∃ (_ : IsLocalRing (AdicCompletion 𝔫 C)) (_ : IsLocalRing (AdicCompletion x (C ⊗[V] D)))
      (_ : Algebra (AdicCompletion 𝔫 C) (AdicCompletion x (C ⊗[V] D)))
      (_ : IsScalarTower C (AdicCompletion 𝔫 C) (AdicCompletion x (C ⊗[V] D)))
      (_ : IsLocalHom (algebraMap (AdicCompletion 𝔫 C) (AdicCompletion x (C ⊗[V] D)))),
      Module.Finite (AdicCompletion 𝔫 C) (AdicCompletion x (C ⊗[V] D)) ∧
      Algebra.Etale (AdicCompletion 𝔫 C) (AdicCompletion x (C ⊗[V] D)) ∧
      (maximalIdeal (AdicCompletion 𝔫 C)).map (algebraMap (AdicCompletion 𝔫 C) (AdicCompletion x (C ⊗[V] D))) =
        maximalIdeal (AdicCompletion x (C ⊗[V] D)) := by p2m_exact_reverting @_root_.P2MW.S_AdicCompletion_exists_moduleFinite_etale_adicCompletion_tensorProduct_of_flat_of_map_maximalIdeal_eq.solution
