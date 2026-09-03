import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemistableCovering_refine_lap_mem_closure_range_lap_of_forall_eq_mul

set_option autoImplicit false

theorem AlgebraicCurve.SemistableCovering.refine_lap_mem_closure_range_lap_of_forall_eq_mul
    (n m : ℕ) (src tgt : Fin m → Fin n) (W : Fin m → ℕ) (hW : ∀ e, 0 < W e) (M : ℕ) (hM : 0 < M)
    (W' : Fin m → ℕ) (hW' : ∀ e, W' e = M * W e) :
    let V := Fin n ⊕ (Σ e : Fin m, Fin (W e - 1))
    let ends : (Σ e : Fin m, Fin (W e)) → V × V := fun ε =>
      (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
       if h1 : ε.2.1 + 1 = W ε.1 then Sum.inl (tgt ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)
    let lap : V → (V → ℤ) := fun v => ∑ ε : Σ e : Fin m, Fin (W e),
      ((if (ends ε).1 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
       (if (ends ε).2 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))
    let V' := Fin n ⊕ (Σ e : Fin m, Fin (W' e - 1))
    let ends' : (Σ e : Fin m, Fin (W' e)) → V' × V' := fun ε =>
      (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
       if h1 : ε.2.1 + 1 = W' ε.1 then Sum.inl (tgt ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)
    let lap' : V' → (V' → ℤ) := fun v => ∑ ε : Σ e : Fin m, Fin (W' e),
      ((if (ends' ε).1 = v then (Pi.single v 1 : V' → ℤ) - (Pi.single (ends' ε).2 1 : V' → ℤ) else 0) +
       (if (ends' ε).2 = v then (Pi.single v 1 : V' → ℤ) - (Pi.single (ends' ε).1 1 : V' → ℤ) else 0))
    let ι : V → V' := Sum.elim (fun i => Sum.inl i) (fun p => Sum.inr ⟨p.1, ⟨M * (p.2.1 + 1) - 1, by
      have h1 := p.2.2; have h2 : M * (p.2.1 + 1) < M * W p.1 := Nat.mul_lt_mul_of_pos_left (by omega) hM
      have h3 : 0 < M * (p.2.1 + 1) := Nat.mul_pos hM (Nat.succ_pos _); have h4 := hW' p.1; omega⟩⟩)
    let ρ : (V → ℤ) →+ (V' → ℤ) := AddMonoidHom.pi fun v' =>
      ∑ v ∈ Finset.univ.filter (fun v => ι v = v'), Pi.evalAddMonoidHom (fun _ : V => ℤ) v
    Function.Injective ι ∧
    (∀ (x : V → ℤ) (v' : V'), ρ x v' = ∑ v ∈ Finset.univ.filter (fun v => ι v = v'), x v) ∧
    (∀ (x : V → ℤ) (v : V), ρ x (ι v) = x v) ∧
    (∀ (x : V → ℤ) (v' : V'), (∀ v, ι v ≠ v') → ρ x v' = 0) ∧
    (∀ (v : V) (c : ℤ), ρ (Pi.single v c) = Pi.single (ι v) c) ∧
    (∀ u : V, ρ (lap u) ∈ AddSubgroup.closure (Set.range lap')) ∧
    AddSubgroup.closure (Set.range lap) ≤ (AddSubgroup.closure (Set.range lap')).comap ρ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemistableCovering_refine_lap_mem_closure_range_lap_of_forall_eq_mul.solution
