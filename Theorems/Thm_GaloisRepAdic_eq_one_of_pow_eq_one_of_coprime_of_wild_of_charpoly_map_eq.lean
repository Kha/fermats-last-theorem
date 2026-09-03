import Definitions.Def_GaloisRep_Adic
import P2M.Util
import P2M.Sol.S_GaloisRepAdic_eq_one_of_pow_eq_one_of_coprime_of_wild_of_charpoly_map_eq

set_option autoImplicit false
open Polynomial

theorem GaloisRepAdic.eq_one_of_pow_eq_one_of_coprime_of_wild_of_charpoly_map_eq
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ρ : GaloisRepAdic A)
    {p : ℕ} (hp : p.Prime) (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A) {q : ℕ} (hq : q.Prime) (hqp : q ≠ p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits)
    {B : Type} [CommRing B] [IsDomain B] (j : A →+* B) (hj : Function.Injective j)
    (a : Bˣ) (ha : (LinearMap.charpoly (ρ.ρ σ)).map j = (X - C ((a : Bˣ) : B)) * (X - C (((a⁻¹ : Bˣ) : B))))
    {n : ℕ} (hn : n.Coprime q) (han : a ^ n = 1) :
    a = 1 := by p2m_exact_reverting @_root_.P2MW.S_GaloisRepAdic_eq_one_of_pow_eq_one_of_coprime_of_wild_of_charpoly_map_eq.solution
