import OMAReductions.R_Erdos985_erdos_985_R2

/-! Prime primitive roots for every odd prime up to 2791, verified by the order criterion. -/

namespace OMA.PrimePrimitiveRoot

-- The order test only needs the prime factors of p - 1.
def certifies (p q : ℕ) : Bool :=
  decide (q.Prime ∧ q < p ∧ q ^ (p - 1) % p = 1 % p) &&
    (p - 1).primeFactorsList.all (fun r => decide (q ^ ((p - 1) / r) % p ≠ 1 % p))

def candidates : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 53]

def checked (p : ℕ) : Bool :=
  decide (p < 3 ∨ p.minFac ≠ p) || candidates.any (certifies p)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem checked_range : ((List.range 2792).all checked) = true := by
  decide +kernel

theorem certifies_sound {p q : ℕ} (hp : p.Prime) (h : certifies p q = true) :
    q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1 := by
  simp only [certifies, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨hq, hlt, hpow⟩, hfactors⟩ := h
  refine ⟨hq, hlt, orderOf_eq_of_pow_and_pow_div_prime (by have := hp.two_le; omega) ?_ ?_⟩
  · simpa only [Nat.cast_pow, Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff' _ _ p).2 hpow
  · intro r hr hd heq
    have hrmem := (Nat.mem_primeFactorsList (by have := hp.two_le; omega : p - 1 ≠ 0)).2 ⟨hr, hd⟩
    apply hfactors r hrmem
    apply (ZMod.natCast_eq_natCast_iff' _ _ p).1
    simpa only [Nat.cast_pow, Nat.cast_one] using heq

end OMA.PrimePrimitiveRoot

open OMA.PrimePrimitiveRoot

theorem OMA.solution : OMA.R_Erdos985_erdos_985_R2.H1 := by
  intro p hp htwo hbound
  have hthree : ¬ p < 3 := by have := hp.two_le; omega
  have h := List.all_eq_true.mp checked_range p (List.mem_range.mpr (by omega))
  simp only [checked, hp.minFac_eq, ne_self_iff_false, hthree, or_self, decide_false,
    Bool.false_or, List.any_eq_true] at h
  obtain ⟨q, _, hq⟩ := h
  exact ⟨q, certifies_sound hp hq⟩
