import OMAReductions.R_Erdos366_erdos_366_variants_weaker_R1

/-!
This finite check refutes the first hypothesis of reduction R1.
In a consecutive pair one member is even, hence divisible by eight if cube-full.
The other member, if it exceeds one and is cube-full, is divisible by the cube
of its least prime factor. Below 100002 this prime is at most 46.
-/

namespace Erdos366Bounded

def hasEvenNeighbour (m : ℕ) : Prop :=
  (8 ∣ m - 1 ∧ Nat.Full 3 (m - 1)) ∨ (8 ∣ m + 1 ∧ Nat.Full 3 (m + 1))

instance (m : ℕ) : Decidable (hasEvenNeighbour m) := by
  unfold hasEvenNeighbour
  infer_instance

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem finite_check : ∀ p : Fin 47, 3 ≤ p.val → p.val.Prime →
    ((List.range (100001 / p.val ^ 3)).all fun j =>
      let m := p.val ^ 3 * (j + 1)
      decide (¬ (hasEvenNeighbour m ∧ Nat.Full 3 m))) = true := by
  decide +kernel

theorem even_cube_dvd {m : ℕ} (hm : m ≠ 0) (he : 2 ∣ m) (hf : Nat.Full 3 m) :
    8 ∣ m :=
  hf 2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, he, hm⟩)

theorem exclude_odd {m : ℕ} (hmin : 1 < m) (hmax : m ≤ 100001)
    (hodd : ¬ 2 ∣ m) (hf : Nat.Full 3 m) (hneigh : hasEvenNeighbour m) : False := by
  let p := m.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hd : p ∣ m := Nat.minFac_dvd m
  have hthree : 3 ≤ p := by
    have := hp.two_le
    by_contra! h
    have : p = 2 := by omega
    exact hodd (this ▸ hd)
  have hc : p ^ 3 ∣ m := hf p (Nat.mem_primeFactors.mpr ⟨hp, hd, by omega⟩)
  have hcap := Nat.le_of_dvd (by omega : 0 < m) hc
  have hsmall : p < 47 := by
    by_contra! h
    have hpow := Nat.pow_le_pow_left h 3
    norm_num at hpow
    omega
  obtain ⟨k, heq⟩ := hc
  cases k with
  | zero => simp_all
  | succ j =>
    have hle : j + 1 ≤ 100001 / p ^ 3 := by
      apply (Nat.le_div_iff_mul_le (pow_pos hp.pos 3)).2
      simpa only [Nat.mul_comm, heq] using hmax
    have ht := List.all_eq_true.mp (finite_check ⟨p, hsmall⟩ hthree hp) j
      (List.mem_range.mpr (show j < 100001 / p ^ 3 from hle))
    have hnot : ¬ (hasEvenNeighbour m ∧ Nat.Full 3 m) := by
      simpa only [← heq, decide_eq_true_eq] using ht
    exact hnot ⟨hneigh, hf⟩

theorem no_small_pair : ¬ OMA.R_Erdos366_erdos_366_variants_weaker_R1.H1 := by
  rintro ⟨n, hn, hnmax, hf, hs⟩
  by_cases he : 2 ∣ n
  · have h8 := even_cube_dvd (by omega) he hf
    apply exclude_odd (m := n + 1) (by omega) (by omega) (by omega) hs
    exact Or.inl (by simpa using And.intro h8 hf)
  · have h8 := even_cube_dvd (m := n + 1) (by omega) (by omega) hs
    exact exclude_odd (m := n) (by omega) (by omega) he hf (Or.inr ⟨h8, hs⟩)

end Erdos366Bounded
