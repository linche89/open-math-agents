import FormalConjectures.ErdosProblems.«21»

/-!
The five small values of the Erdős–Lovász extremal function.
This file assembles the reduction and both step proofs by zarnab222-dev:
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1129
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1179
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/1318
Only the names of the two step conclusions and the final application differ from the sources.
-/

-- Credit: @zarnab222-dev
namespace OMA.R_Erdos21_erdos_21_variants_small_values_R1

open Erdos21

private theorem minimum_eq {n m : ℕ}
    (hw : ∃ F : Finset (Finset ℕ), IsErdosLovaszFamily n F ∧ F.card = m)
    (hl : ∀ F : Finset (Finset ℕ), IsErdosLovaszFamily n F → m ≤ F.card) : f n = m := by
  apply IsLeast.csInf_eq
  exact ⟨hw, fun k ⟨F, hF, hcard⟩ => hcard ▸ hl F hF⟩

private theorem order_one : f 1 = 1 := by
  apply minimum_eq
  · refine ⟨{{0}}, ⟨by decide, by decide, ?_⟩, by decide⟩
    intro S hS
    have : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst S
    exact ⟨{0}, by decide, by simp⟩
  · intro F hF
    obtain ⟨A, hA, _⟩ := hF.2.2 ∅ (by simp)
    exact Finset.card_pos.mpr ⟨A, hA⟩

private theorem order_two : f 2 = 3 := by
  apply minimum_eq
  · refine ⟨{{0, 1}, {0, 2}, {1, 2}}, ⟨by decide, by decide, ?_⟩, by decide⟩
    intro S hS
    obtain ⟨v, hv⟩ := Finset.card_le_one_iff_subset_singleton.mp hS
    by_cases h0 : v = 0
    · exact ⟨{1, 2}, by decide, Finset.disjoint_of_subset_left hv (by simp [h0])⟩
    by_cases h1 : v = 1
    · exact ⟨{0, 2}, by decide, Finset.disjoint_of_subset_left hv (by simp [h1])⟩
    · exact ⟨{0, 1}, by decide, Finset.disjoint_of_subset_left hv (by simp [h0, h1])⟩
  · intro F hF
    obtain ⟨A, hA, _⟩ := hF.2.2 ∅ (by simp)
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by rw [hF.1 A hA]; decide)
    obtain ⟨B, hB, hdisB⟩ := hF.2.2 {x} (by simp)
    have hAB : A ≠ B := fun h => Finset.disjoint_singleton_left.mp hdisB (h ▸ hx)
    obtain ⟨y, hy⟩ := hF.2.1 A hA B hB
    obtain ⟨hyA, hyB⟩ := Finset.mem_inter.mp hy
    obtain ⟨C, hC, hdisC⟩ := hF.2.2 {y} (by simp)
    have hyC := Finset.disjoint_singleton_left.mp hdisC
    have hAC : A ≠ C := fun h => hyC (h ▸ hyA)
    have hBC : B ≠ C := fun h => hyC (h ▸ hyB)
    calc
      3 = ({A, B, C} : Finset (Finset ℕ)).card := by simp [hAB, hAC, hBC]
      _ ≤ F.card := Finset.card_le_card (by
        rw [Finset.insert_subset_iff, Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨hA, hB, hC⟩)

/-- In an intersecting family, any subfamily of at most two edges has a common vertex. -/
private theorem pair_cover {F G : Finset (Finset ℕ)} (hF : IsErdosLovaszFamily 3 F)
    (hG : G ⊆ F) (hs : G.card ≤ 2) : ∃ y : ℕ, ∀ E ∈ G, y ∈ E := by
  by_cases ht : G.card = 2
  · obtain ⟨A, B, _, rfl⟩ := Finset.card_eq_two.mp ht
    obtain ⟨y, hy⟩ := hF.2.1 A (hG (by simp)) B (hG (by simp))
    refine ⟨y, ?_⟩
    simpa using Finset.mem_inter.mp hy
  by_cases ho : G.card = 1
  · obtain ⟨A, rfl⟩ := Finset.card_eq_one.mp ho
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (by rw [hF.1 A (hG (by simp))]; decide)
    exact ⟨y, by simpa using hy⟩
  have hempty : G = ∅ := Finset.card_eq_zero.mp (by omega)
  exact ⟨0, by simp [hempty]⟩

private theorem lower_three (F : Finset (Finset ℕ)) (hF : IsErdosLovaszFamily 3 F) :
    6 ≤ F.card := by
  by_contra! hsmall
  -- At least three edges avoid each vertex, or a second vertex covers the rest.
  have miss (x : ℕ) : 3 ≤ (F.filter fun E => x ∉ E).card := by
    by_contra! h
    obtain ⟨y, hy⟩ := pair_cover hF (Finset.filter_subset _ F) (by omega : (F.filter fun E => x ∉ E).card ≤ 2)
    obtain ⟨E, hE, hd⟩ := hF.2.2 {x, y} Finset.card_le_two
    have hx : x ∉ E := fun hxE => Finset.disjoint_left.mp hd (by simp) hxE
    exact Finset.disjoint_left.mp hd (by simp : y ∈ ({x, y} : Finset ℕ)) (hy E (Finset.mem_filter.mpr ⟨hE, hx⟩))
  have degree (x : ℕ) : (F.filter fun E => x ∈ E).card ≤ 2 := by
    have := F.card_filter_add_card_filter_not (fun E => x ∈ E)
    have := miss x
    omega
  obtain ⟨A, hA, _⟩ := hF.2.2 ∅ (by simp)
  -- Each vertex of A can account for at most one further edge meeting A.
  let others (x : ℕ) := (F.erase A).filter fun E => x ∈ E
  have hcap (x : ℕ) (hx : x ∈ A) : (others x).card ≤ 1 := by
    rw [show others x = (F.filter fun E => x ∈ E).erase A from Finset.filter_erase ..,
      Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hA, hx⟩)]
    have := degree x
    omega
  have hsub : F.erase A ⊆ A.biUnion others := by
    intro E hE
    obtain ⟨y, hy⟩ := hF.2.1 A hA E (Finset.mem_of_mem_erase hE)
    exact Finset.mem_biUnion.mpr ⟨y, (Finset.mem_inter.mp hy).1,
      Finset.mem_filter.mpr ⟨hE, (Finset.mem_inter.mp hy).2⟩⟩
  have hbound := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le_card_mul A others 1 hcap)
  rw [Finset.card_erase_of_mem hA, hF.1 A hA, mul_one] at hbound
  -- Two distinct intersecting edges supply a vertex meeting at least two edges.
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by rw [hF.1 A hA]; decide)
  obtain ⟨B, hB, hdis⟩ := hF.2.2 {a} (by simp)
  have hAB : A ≠ B := fun he => Finset.disjoint_singleton_left.mp hdis (he ▸ ha)
  obtain ⟨z, hz⟩ := hF.2.1 A hA B hB
  have hp : ({A, B} : Finset (Finset ℕ)) ⊆ F.filter (fun E => z ∈ E) := by
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨Finset.mem_filter.mpr ⟨hA, (Finset.mem_inter.mp hz).1⟩,
      Finset.mem_filter.mpr ⟨hB, (Finset.mem_inter.mp hz).2⟩⟩
  have hdeg := Finset.card_le_card hp
  simp only [Finset.card_pair hAB] at hdeg
  have := F.card_filter_add_card_filter_not (fun E => z ∈ E)
  have := miss z
  omega

-- The order-four and order-five families use the incidence matrices in
-- János Barát, arXiv:2011.04444, sections 6.1 and 6.2.
private theorem verify_family {n : ℕ} {F : Finset (Finset ℕ)} (V : Finset ℕ)
    (hsize : n - 1 ≤ V.card) (hinside : ∀ A ∈ F, A ⊆ V)
    (huniform : ∀ A ∈ F, A.card = n)
    (hpairs : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty)
    (hmiss : ∀ T ∈ V.powersetCard (n - 1), ∃ A ∈ F, Disjoint T A) :
    IsErdosLovaszFamily n F := by
  refine ⟨huniform, hpairs, ?_⟩
  intro S hS
  obtain ⟨T, hST, hTV, hcard⟩ := Finset.exists_subsuperset_card_eq
    (Finset.inter_subset_right : S ∩ V ⊆ V)
    ((Finset.card_le_card Finset.inter_subset_left).trans hS) hsize
  obtain ⟨A, hA, hd⟩ := hmiss T (Finset.mem_powersetCard.mpr ⟨hTV, hcard⟩)
  refine ⟨A, hA, Finset.disjoint_left.mpr ?_⟩
  intro x hxS hxA
  exact Finset.disjoint_left.mp hd (hST (Finset.mem_inter.mpr ⟨hxS, hinside A hA hxA⟩)) hxA

-- Six lines of the Fano plane remain after deleting a line.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem witness_three :
    ∃ F : Finset (Finset ℕ), IsErdosLovaszFamily 3 F ∧ F.card = 6 := by
  refine ⟨{{1, 3, 5},
      {0, 3, 4},
      {2, 3, 6},
      {0, 1, 2},
      {1, 4, 6},
      {0, 5, 6}}, ?_, by decide +kernel⟩
  apply verify_family (Finset.range 7) <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem witness_four :
    ∃ F : Finset (Finset ℕ), IsErdosLovaszFamily 4 F ∧ F.card = 9 := by
  refine ⟨{{0, 1, 2, 3},
      {0, 4, 5, 6},
      {0, 7, 8, 9},
      {1, 4, 7, 10},
      {1, 2, 5, 8},
      {2, 6, 9, 10},
      {3, 4, 6, 8},
      {3, 5, 7, 9},
      {0, 3, 5, 10}}, ?_, by decide +kernel⟩
  apply verify_family (Finset.range 11) <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem witness_five :
    ∃ F : Finset (Finset ℕ), IsErdosLovaszFamily 5 F ∧ F.card = 13 := by
  refine ⟨{{0, 1, 2, 3, 4},
      {0, 1, 5, 6, 7},
      {0, 2, 8, 9, 10},
      {0, 5, 8, 11, 12},
      {2, 5, 13, 14, 15},
      {3, 6, 8, 13, 16},
      {4, 5, 9, 10, 13},
      {2, 4, 6, 11, 12},
      {4, 7, 8, 14, 16},
      {3, 7, 9, 11, 15},
      {1, 10, 12, 15, 16},
      {1, 6, 9, 11, 14},
      {3, 7, 10, 12, 14}}, ?_, by decide +kernel⟩
  apply verify_family (Finset.range 17) <;> decide +kernel

/-- Rule out order-four families with at most eight edges. -/
def H1 : Prop := ∀ F : Finset (Finset ℕ), IsErdosLovaszFamily 4 F → 9 ≤ F.card

/-- Rule out order-five families with at most twelve edges. -/
def H2 : Prop := ∀ F : Finset (Finset ℕ), IsErdosLovaszFamily 5 F → 13 ≤ F.card

theorem main : H1 → H2 → type_of% @Erdos21.erdos_21.variants.small_values := by
  intro lower_four lower_five
  exact ⟨order_one, order_two, minimum_eq witness_three lower_three,
    minimum_eq witness_four lower_four, minimum_eq witness_five lower_five⟩

end OMA.R_Erdos21_erdos_21_variants_small_values_R1

/-! An intersecting family of eight four-element edges always has a three-point cover. The argument counts pairs of degree-three vertices in the eight indexed edges. -/

open Finset Erdos21

namespace OrderFour

private theorem hit_pair (E : Fin 8 → Finset ℕ)
    (cross : ∀ i j, (E i ∩ E j).Nonempty) (t : Finset (Fin 8)) (ht : t.card ≤ 2) :
    ∃ x : ℕ, ∀ i ∈ t, x ∈ E i := by
  by_cases htwo : t.card = 2
  · obtain ⟨a, b, _, rfl⟩ := card_eq_two.mp htwo
    obtain ⟨x, hx⟩ := cross a b
    exact ⟨x, by simpa using mem_inter.mp hx⟩
  by_cases hone : t.card = 1
  · obtain ⟨a, rfl⟩ := card_eq_one.mp hone
    obtain ⟨x, hx⟩ := cross a a
    exact ⟨x, by simpa using (mem_inter.mp hx).1⟩
  have : t = ∅ := card_eq_zero.mp (by omega)
  exact ⟨0, by simp [this]⟩

private theorem hit_four (E : Fin 8 → Finset ℕ)
    (cross : ∀ i j, (E i ∩ E j).Nonempty) (t : Finset (Fin 8)) (ht : t.card ≤ 4) :
    ∃ x y : ℕ, ∀ i ∈ t, x ∈ E i ∨ y ∈ E i := by
  obtain ⟨a, hat, ha⟩ := exists_subset_card_eq (s := t) (n := min 2 t.card) (min_le_right ..)
  obtain ⟨x, hx⟩ := hit_pair E cross a (ha.trans_le (min_le_left ..))
  obtain ⟨y, hy⟩ := hit_pair E cross (t \ a) (by rw [card_sdiff_of_subset hat, ha]; omega)
  exact ⟨x, y, fun i hi => by
    by_cases h : i ∈ a
    · exact Or.inl (hx i h)
    · exact Or.inr (hy i (mem_sdiff.mpr ⟨hi,h⟩))⟩

private theorem count_by_edges (D : Finset ℕ) (E : Fin 8 → Finset ℕ) (w : Fin 8 → ℕ) :
    ∑ x ∈ D, ∑ i ∈ univ.filter (fun i => x ∈ E i), w i =
      ∑ i, (D.filter fun x => x ∈ E i).card * w i := by
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [← sum_const_nat (s := D.filter fun x => x ∈ E i) (f := fun _ => w i) (fun _ _ => rfl)]
  rw [sum_filter]

private theorem eight_impossible (E : Fin 8 → Finset ℕ)
    (size : ∀ i, (E i).card = 4) (cross : ∀ i j, (E i ∩ E j).Nonempty)
    (miss : ∀ S : Finset ℕ, S.card ≤ 3 → ∃ i, Disjoint S (E i)) : False := by
  classical
  let bag (x : ℕ) := univ.filter (fun i => x ∈ E i)
  let V := univ.biUnion E
  let D := V.filter (fun x => (bag x).card = 3)
  let row (i : Fin 8) := D.filter (fun x => x ∈ E i)
  let k (i : Fin 8) := (row i).card
  have inbag {x i} : i ∈ bag x ↔ x ∈ E i := by simp [bag]
  have hdeg (x : ℕ) : (bag x).card ≤ 3 := by
    by_contra! h
    obtain ⟨y,z,hyz⟩ := hit_four E cross (univ \ bag x) (by
      rw [card_sdiff_of_subset (subset_univ _)]
      simpa using (show 8 - (bag x).card ≤ 4 by omega))
    obtain ⟨i, hi⟩ := miss {x,y,z} card_le_three
    have hnx : x ∉ E i := fun h => disjoint_left.mp hi (by simp) h
    rcases hyz i (mem_sdiff.mpr ⟨mem_univ _, fun h => hnx (inbag.mp h)⟩) with h | h
    · exact disjoint_left.mp hi (by simp : y ∈ ({x,y,z} : Finset ℕ)) h
    · exact disjoint_left.mp hi (by simp : z ∈ ({x,y,z} : Finset ℕ)) h
  have hd {x} (hx : x ∈ D) : (bag x).card = 3 := (mem_filter.mp hx).2
  have share {x y} (hx : x ∈ D) (hy : y ∈ D) : ∃ i, x ∈ E i ∧ y ∈ E i := by
    by_contra! h
    have hxy : Disjoint (bag x) (bag y) := disjoint_left.mpr fun i hi hj =>
      h i (inbag.mp hi) (inbag.mp hj)
    have sze : (bag x ∪ bag y).card = 6 := by rw [card_union_of_disjoint hxy, hd hx, hd hy]
    obtain ⟨z,hz⟩ := hit_pair E cross (univ \ (bag x ∪ bag y)) (by
      rw [card_sdiff_of_subset (subset_univ _), sze]; decide)
    obtain ⟨i,hi⟩ := miss {x,y,z} card_le_three
    have nx : i ∉ bag x := fun h => disjoint_left.mp hi (by simp) (inbag.mp h)
    have ny : i ∉ bag y := fun h => disjoint_left.mp hi (by simp) (inbag.mp h)
    exact disjoint_left.mp hi (by simp : z ∈ ({x,y,z} : Finset ℕ))
      (hz i (by simp [nx, ny]))
  have le_four (i) : k i ≤ 4 := (card_le_card (show row i ⊆ E i from
    fun _ h => (mem_filter.mp h).2)).trans_eq (size i)
  -- Each edge meets seven others, so at least three of its four vertices have degree three.
  have three_le (i : Fin 8) : 3 ≤ k i := by
    let neighbors (x : ℕ) := (bag x).erase i
    have hcover : univ.erase i ⊆ (E i).biUnion neighbors := by
      intro j hj
      obtain ⟨x, hx⟩ := cross i j
      exact mem_biUnion.mpr ⟨x, (mem_inter.mp hx).1,
        mem_erase.mpr ⟨(mem_erase.mp hj).1, inbag.mpr (mem_inter.mp hx).2⟩⟩
    have limit (x : ℕ) (hx : x ∈ E i) : (neighbors x).card ≤ (if x ∈ D then 1 else 0) + 1 := by
      have hV : x ∈ V := mem_biUnion.mpr ⟨i, mem_univ _, hx⟩
      rw [show neighbors x = (bag x).erase i from rfl, card_erase_of_mem (inbag.mpr hx)]
      by_cases hD : x ∈ D
      · simp [hD, hd hD]
      · have hn : (bag x).card ≠ 3 := fun h => hD (mem_filter.mpr ⟨hV, h⟩)
        simp [hD]; have := hdeg x; omega
    have h := (card_le_card hcover).trans (card_biUnion_le.trans (sum_le_sum limit))
    have eqrow : E i ∩ D = row i := by ext a; simp [row, and_comm]
    simp [sum_add_distrib, card_erase_of_mem (mem_univ i), size i, eqrow, k] at h ⊢
    omega
  -- Every two degree-three vertices share an edge. Count the other vertices from each of them.
  have count (x) (hx : x ∈ D) : D.card - 1 ≤ ∑ i ∈ bag x, (k i - 1) := by
    let incident (i : Fin 8) := (row i).erase x
    have hsub : D.erase x ⊆ (bag x).biUnion incident := by
      intro y hy
      obtain ⟨i,hix,hiy⟩ := share hx (mem_erase.mp hy).2
      exact mem_biUnion.mpr ⟨i,inbag.mpr hix,mem_erase.mpr
        ⟨(mem_erase.mp hy).1,mem_filter.mpr ⟨(mem_erase.mp hy).2,hiy⟩⟩⟩
    rw [← card_erase_of_mem hx]
    refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
    apply sum_le_sum
    intro i hi
    exact (card_erase_of_mem (s := row i) (a := x) (mem_filter.mpr ⟨hx,inbag.mp hi⟩)).le
  have hdouble := sum_le_sum count
  have highcount := count_by_edges D E (fun _ => 1)
  have hpairs := count_by_edges D E (fun i => k i - 1)
  change (∑ x ∈ D, ∑ i ∈ bag x, 1) = ∑ i, k i * 1 at highcount
  simp only [sum_const, smul_eq_mul, mul_one] at highcount
  rw [sum_const_nat (m := 3) (fun x hx => hd hx)] at highcount
  change (∑ _x ∈ D, (D.card - 1)) ≤ ∑ x ∈ D, ∑ i ∈ bag x, (k i - 1) at hdouble
  change (∑ x ∈ D, ∑ i ∈ bag x, (k i - 1)) = ∑ i, k i * (k i - 1) at hpairs
  rw [hpairs, sum_const, smul_eq_mul] at hdouble
  -- For a row containing k = 3 or 4 such vertices, k(k − 1) = 6k − 12.
  have eqn : (∑ i, (k i * (k i - 1) + 12)) = ∑ i, 6 * k i := by
    apply sum_congr rfl
    intro i _
    have ha := three_le i
    have hb := le_four i
    rcases (by omega : k i = 3 ∨ k i = 4) with h | h <;> simp [h]
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
    ← mul_sum, ← highcount] at eqn
  have sumle : ∑ i, k i ≤ ∑ _ : Fin 8, 4 := sum_le_sum (fun i _ => le_four i)
  rw [← highcount] at sumle
  norm_num at sumle
  generalize hD : D.card = d at hdouble eqn sumle
  have : d ≤ 10 := by omega
  interval_cases d <;> omega

theorem lower_four (F : Finset (Finset ℕ)) (hF : IsErdosLovaszFamily 4 F) :
    9 ≤ F.card := by
  classical
  by_contra! hsmall
  obtain ⟨A, hA, _⟩ := hF.2.2 ∅ (by simp)
  let e := Fintype.equivFin (↥F)
  let gen (i : Fin 8) : ↥F :=
    if hi : i.val < Fintype.card (↥F) then e.symm ⟨i.val, hi⟩ else ⟨A,hA⟩
  have onto (B : ↥F) : ∃ i, gen i = B := by
    have hi := (e B).isLt
    have hb : (e B).val < 8 := by simp at hi; omega
    exact ⟨⟨(e B).val, hb⟩, by simp only [gen, dif_pos (e B).isLt, Fin.eta, Equiv.symm_apply_apply]⟩
  apply eight_impossible (fun i => (gen i).val)
    (fun i => hF.1 _ (gen i).property)
    (fun i j => hF.2.1 _ (gen i).property _ (gen j).property)
  intro S hS
  obtain ⟨B,hB,hd⟩ := hF.2.2 S hS
  obtain ⟨i,hi⟩ := onto ⟨B,hB⟩
  exact ⟨i, by simpa [hi] using hd⟩

end OrderFour


theorem OMA.orderFourLowerBound : OMA.R_Erdos21_erdos_21_variants_small_values_R1.H1 :=
  OrderFour.lower_four

/-!
A lower bound of thirteen edges in the order-five Erdős–Lovász problem.

A family on at most twelve edges must have exactly twelve, with a vertex of degree
four. The eight edges avoiding it require four vertices to hit. Their three-edge
stars therefore meet pairwise, and each of the eight edge indices must be the
singleton intersection of two stars. After normalizing one such pair of triples,
a finite check on the three indices outside its union rules this out.

For the known extremal value see Barát, arXiv:2011.04444, §6.2. For the general
singleton-intersection parameter for triples see Talbot, arXiv:math/0306119.
-/

-- Credit: @zarnab222-dev

open Finset Erdos21

namespace OrderFive

private theorem hit_pair {F G : Finset (Finset ℕ)} (hF : IsErdosLovaszFamily 5 F)
    (hG : G ⊆ F) (h : G.card ≤ 2) : ∃ x, ∀ A ∈ G, x ∈ A := by
  by_cases h2 : G.card = 2
  · obtain ⟨A, B, _, rfl⟩ := card_eq_two.mp h2
    obtain ⟨x,hx⟩ := hF.2.1 A (hG (by simp)) B (hG (by simp))
    exact ⟨x, by simpa using mem_inter.mp hx⟩
  by_cases h1 : G.card = 1
  · obtain ⟨A,rfl⟩ := card_eq_one.mp h1
    obtain ⟨x,hx⟩ := card_pos.mp (by rw [hF.1 A (hG (by simp))]; decide)
    exact ⟨x,by simpa using hx⟩
  have hem : G = ∅ := card_eq_zero.mp (by omega)
  exact ⟨0,by simp [hem]⟩

private theorem cover_pairs {F : Finset (Finset ℕ)} (hF : IsErdosLovaszFamily 5 F)
    (k : ℕ) (G : Finset (Finset ℕ)) (hG : G ⊆ F) (hs : G.card ≤ 2*k) :
    ∃ S : Finset ℕ, S.card ≤ k ∧ ∀ A ∈ G, (S ∩ A).Nonempty := by
  induction k generalizing G with
  | zero =>
    have h : G = ∅ := card_eq_zero.mp (by omega)
    exact ⟨∅,by simp,by simp [h]⟩
  | succ k ih =>
    obtain ⟨P,hPG,hP⟩ := exists_subset_card_eq (s := G) (n := min 2 G.card) (min_le_right ..)
    obtain ⟨x,hx⟩ := hit_pair hF (hPG.trans hG) (hP.trans_le (min_le_left ..))
    obtain ⟨S,hsize,hcover⟩ := ih (G \ P) (sdiff_subset.trans hG)
      (by rw [card_sdiff_of_subset hPG,hP]; omega)
    refine ⟨insert x S,(card_insert_le ..).trans (by omega),?_⟩
    intro A hA
    by_cases ha : A ∈ P
    · exact ⟨x,mem_inter.mpr ⟨mem_insert_self ..,hx A ha⟩⟩
    · obtain ⟨y,hy⟩ := hcover A (mem_sdiff.mpr ⟨hA,ha⟩)
      exact ⟨y,mem_inter.mpr ⟨mem_insert_of_mem (mem_inter.mp hy).1,(mem_inter.mp hy).2⟩⟩

private theorem neighbors {F G : Finset (Finset ℕ)} (hF : IsErdosLovaszFamily 5 F)
    (hG : G ⊆ F) {A : Finset ℕ} (hA : A ∈ G) :
    G.card - 1 ≤ ∑ x ∈ A, ((G.filter fun B => x ∈ B).card - 1) := by
  let N (x : ℕ) := (G.filter fun B => x ∈ B).erase A
  have hsub : G.erase A ⊆ A.biUnion N := by
    intro B hB
    have hb := mem_erase.mp hB
    obtain ⟨x,hx⟩ := hF.2.1 A (hG hA) B (hG hb.2)
    exact mem_biUnion.mpr ⟨x,(mem_inter.mp hx).1,mem_erase.mpr ⟨hb.1,mem_filter.mpr ⟨hb.2,(mem_inter.mp hx).2⟩⟩⟩
  rw [← card_erase_of_mem hA]
  apply (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  exact sum_le_sum (fun x hx => (card_erase_of_mem (mem_filter.mpr ⟨hA,hx⟩)).le)

-- Among seven edges, any one meets six others at its five vertices. A vertex on
-- three edges and one common point from each of two remaining pairs suffice.
private theorem cover_seven {F G : Finset (Finset ℕ)} (hF : IsErdosLovaszFamily 5 F)
    (hG : G ⊆ F) (h7 : G.card ≤ 7) :
    ∃ S : Finset ℕ, S.card ≤ 3 ∧ ∀ A ∈ G, (S ∩ A).Nonempty := by
  by_cases h6 : G.card ≤ 6
  · exact cover_pairs hF 3 G hG h6
  obtain ⟨A,hA⟩ := card_pos.mp (by omega : 0 < G.card)
  obtain ⟨x,hx,hx3⟩ : ∃ x ∈ A, 3 ≤ (G.filter fun B => x ∈ B).card := by
    by_contra! hn
    have h := (neighbors hF hG hA).trans (sum_le_sum (g := fun _ => 1)
      (by intro x hx; have := hn x hx; omega))
    simp [hF.1 A (hG hA)] at h
    omega
  have hsplit := G.card_filter_add_card_filter_not (fun B => x ∈ B)
  obtain ⟨S,hS,hcover⟩ := cover_pairs hF 2 (G.filter fun B => x ∉ B) ((filter_subset ..).trans hG) (by omega)
  refine ⟨insert x S,(card_insert_le ..).trans (by omega),?_⟩
  intro B hB
  by_cases h : x ∈ B
  · exact ⟨x,mem_inter.mpr ⟨mem_insert_self ..,h⟩⟩
  · obtain ⟨y,hy⟩ := hcover B (mem_filter.mpr ⟨hB,h⟩)
    exact ⟨y,mem_inter.mpr ⟨mem_insert_of_mem (mem_inter.mp hy).1,(mem_inter.mp hy).2⟩⟩

private theorem degree_limit {F : Finset (Finset ℕ)} (hF : IsErdosLovaszFamily 5 F) (x : ℕ) :
    (F.filter fun A => x ∈ A).card + 8 ≤ F.card := by
  by_contra! h
  have hh := F.card_filter_add_card_filter_not (fun A => x ∈ A)
  obtain ⟨S,hS,hcover⟩ := cover_seven hF (filter_subset ..) (by omega : (F.filter fun A => x ∉ A).card ≤ 7)
  obtain ⟨A,hA,hd⟩ := hF.2.2 (insert x S) ((card_insert_le ..).trans (by omega))
  have hx : x ∉ A := fun h => disjoint_left.mp hd (mem_insert_self ..) h
  obtain ⟨y,hy⟩ := hcover A (mem_filter.mpr ⟨hA,hx⟩)
  exact disjoint_left.mp hd (mem_insert_of_mem (mem_inter.mp hy).1) (mem_inter.mp hy).2

private theorem incidence {F : Finset (Finset ℕ)} (w : ℕ → ℕ) :
    ∑ x ∈ F.biUnion id, (F.filter fun A => x ∈ A).card * w x =
      ∑ A ∈ F, ∑ x ∈ A, w x := by
  calc
    _ = ∑ x ∈ F.biUnion id, ∑ A ∈ F, if x ∈ A then w x else 0 := by
      apply sum_congr rfl
      intro x _
      rw [← sum_filter, sum_const, smul_eq_mul]
    _ = ∑ A ∈ F, ∑ x ∈ F.biUnion id, if x ∈ A then w x else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro A hA
      rw [← sum_filter]
      congr 1
      ext x
      simp only [mem_filter, and_iff_right_iff_imp]
      exact fun hx => mem_biUnion.mpr ⟨A,hA,hx⟩

-- At eleven edges, every vertex must have degree three. The incidence count
-- would then make 55 divisible by three.
private theorem twelve_le (F : Finset (Finset ℕ)) (hF : IsErdosLovaszFamily 5 F) : 12 ≤ F.card := by
  by_contra! h
  let d (x : ℕ) := (F.filter fun A => x ∈ A).card
  have bound (x : ℕ) := degree_limit hF x
  obtain ⟨A,hA,_⟩ := hF.2.2 ∅ (by simp)
  have h11 : F.card = 11 := by
    by_contra hn
    have hnear := (neighbors hF Subset.rfl hA).trans (sum_le_sum (g := fun _ => F.card-9)
      (by intro x hx; have := bound x; omega))
    simp [hF.1 A hA] at hnear
    have := bound 0
    omega
  have all_three (x : ℕ) (hx : x ∈ F.biUnion id) : d x = 3 := by
    have hmax := bound x
    have hmax' : d x ≤ 3 := by dsimp [d]; omega
    by_contra hne
    obtain ⟨B,hB,hxB⟩ := mem_biUnion.mp hx
    change x ∈ B at hxB
    have hnear := neighbors hF Subset.rfl hB
    change F.card - 1 ≤ ∑ y ∈ B, (d y - 1) at hnear
    have hrest : ∑ y ∈ B.erase x, (d y - 1) ≤ ∑ _ ∈ B.erase x, 2 := sum_le_sum
      (fun y _ => by dsimp [d]; have := bound y; omega)
    rw [← add_sum_erase _ _ hxB] at hnear
    simp [card_erase_of_mem hxB,hF.1 B hB] at hrest
    omega
  have hsum := incidence (F := F) (fun _ => 1)
  simp only [mul_one,sum_const,smul_eq_mul] at hsum
  change (∑ x ∈ F.biUnion id, d x) = ∑ A ∈ F, A.card at hsum
  rw [sum_const_nat (m := 3) (fun x hx => all_three x hx),
    sum_const_nat (m := 5) (fun A hA => hF.1 A hA), h11] at hsum
  omega

end OrderFive

namespace EightResidual

private theorem pairCover {α : Type*} [DecidableEq α] (row : Fin 8 → Finset α)
    (meet : ∀ i j, (row i ∩ row j).Nonempty) (fallback : α)
    (k : ℕ) (G : Finset (Fin 8)) (hs : G.card ≤ 2*k) :
    ∃ S : Finset α, S.card ≤ k ∧ ∀ i ∈ G, (S ∩ row i).Nonempty := by
  have pair (P : Finset (Fin 8)) (hP : P.card ≤ 2) : ∃ a, ∀ i ∈ P, a ∈ row i := by
    by_cases h : P.card = 2
    · obtain ⟨i,j,_,rfl⟩ := card_eq_two.mp h
      obtain ⟨a,ha⟩ := meet i j
      exact ⟨a,by simpa using mem_inter.mp ha⟩
    by_cases h' : P.card = 1
    · obtain ⟨i,rfl⟩ := card_eq_one.mp h'
      obtain ⟨a,ha⟩ := meet i i
      exact ⟨a,by simpa using (mem_inter.mp ha).1⟩
    have hem : P = ∅ := card_eq_zero.mp (by omega)
    exact ⟨fallback,by simp [hem]⟩
  induction k generalizing G with
  | zero =>
    have h : G = ∅ := card_eq_zero.mp (by omega)
    exact ⟨∅,by simp,by simp [h]⟩
  | succ k ih =>
    obtain ⟨P,hPG,hP⟩ := exists_subset_card_eq (s := G) (n := min 2 G.card) (min_le_right ..)
    obtain ⟨a,ha⟩ := pair P (hP.trans_le (min_le_left ..))
    obtain ⟨S,hsize,hcover⟩ := ih (G \ P) (by rw [card_sdiff_of_subset hPG,hP]; omega)
    refine ⟨insert a S,(card_insert_le ..).trans (by omega),?_⟩
    intro i hi
    by_cases hp : i ∈ P
    · exact ⟨a,mem_inter.mpr ⟨mem_insert_self ..,ha i hp⟩⟩
    · obtain ⟨b,hb⟩ := hcover i (mem_sdiff.mpr ⟨hi,hp⟩)
      exact ⟨b,mem_inter.mpr ⟨mem_insert_of_mem (mem_inter.mp hb).1,(mem_inter.mp hb).2⟩⟩

theorem residual {α : Type*} [DecidableEq α] {F : Finset (Finset α)}
    (h12 : F.card = 12) (hsize : ∀ A ∈ F, A.card = 5)
    (hinter : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty)
    (hmiss : ∀ S : Finset α, S.card ≤ 4 → ∃ A ∈ F, Disjoint S A)
    (x : α) (hx : (F.filter (x ∈ ·)).card = 4) :
    ∃ T : Finset (Finset (Fin 8)),
      (∀ A ∈ T, A.card = 3) ∧ (∀ A ∈ T, ∀ B ∈ T, (A ∩ B).Nonempty) ∧
      (∀ i : Fin 8, ∃ A ∈ T, ∃ B ∈ T, A ∩ B = {i}) := by
  classical
  let R := F.filter (fun A => x ∉ A)
  have hR : R.card = 8 := by
    have := F.card_filter_add_card_filter_not (fun A => x ∈ A)
    dsimp [R]
    omega
  let e : Fin 8 ≃ R := (Fintype.equivFinOfCardEq (by simpa using hR)).symm
  let row (i : Fin 8) : Finset α := e i
  let star (y : α) := univ.filter fun i => y ∈ row i
  have inStar (i : Fin 8) (y : α) : i ∈ star y ↔ y ∈ row i := by simp [star]
  have rowF (i : Fin 8) : row i ∈ F := (mem_filter.mp (e i).property).1
  have meet (i j : Fin 8) := hinter _ (rowF i) _ (rowF j)
  have size (i : Fin 8) := hsize _ (rowF i)
  have miss (S : Finset α) (hS : S.card ≤ 3) : ∃ i, Disjoint S (row i) := by
    obtain ⟨A,hA,hd⟩ := hmiss (insert x S) ((card_insert_le ..).trans (by omega))
    have hxA : x ∉ A := fun ha => disjoint_left.mp hd (mem_insert_self ..) ha
    have haR : A ∈ R := mem_filter.mpr ⟨hA,hxA⟩
    refine ⟨e.symm ⟨A,haR⟩,?_⟩
    simp only [row,Equiv.apply_symm_apply]
    exact hd.mono_left (subset_insert ..)
  have budget (P : Finset α) (k : ℕ) (hk : P.card + k ≤ 3) :
      2*k < (univ \ P.biUnion star).card := by
    by_contra! h
    obtain ⟨S,hS,hit⟩ := pairCover row meet x k _ h
    obtain ⟨i,hd⟩ := miss (P ∪ S) ((card_union_le ..).trans (by omega))
    have hi : i ∈ univ \ P.biUnion star := by
      refine mem_sdiff.mpr ⟨mem_univ _,fun hmem => ?_⟩
      obtain ⟨y,hy,hyi⟩ := mem_biUnion.mp hmem
      exact disjoint_left.mp hd (mem_union_left _ hy) ((inStar i y).mp hyi)
    obtain ⟨b,hb⟩ := hit i hi
    exact disjoint_left.mp hd (mem_union_right _ (mem_inter.mp hb).1) (mem_inter.mp hb).2
  have cap (y : α) : (star y).card ≤ 3 := by
    have h := budget {y} 2 (by simp)
    simp only [singleton_biUnion,card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin] at h
    omega
  have triplesMeet {a b : α} (ha : (star a).card = 3) (hb : (star b).card = 3) :
      (star a ∩ star b).Nonempty := by
    by_contra! hn
    have hd : Disjoint (star a) (star b) := disjoint_iff_inter_eq_empty.mpr hn
    have hab : a ≠ b := by
      rintro rfl
      have := disjoint_self.mp hd
      simp [this] at ha
    have ht := budget {a,b} 1 (by simp [hab])
    simp only [biUnion_insert,singleton_biUnion,card_sdiff_of_subset (subset_univ _),
      card_union_of_disjoint hd,card_univ,Fintype.card_fin,ha,hb] at ht
    omega
  have first (i : Fin 8) : ∃ z ∈ row i, (star z).card = 3 := by
    by_contra! hn
    have sub : univ.erase i ⊆ (row i).biUnion (fun y => (star y).erase i) := by
      intro j hj
      obtain ⟨y,hy⟩ := meet i j
      exact mem_biUnion.mpr ⟨y,(mem_inter.mp hy).1,mem_erase.mpr ⟨(mem_erase.mp hj).1,
        (inStar j y).mpr (mem_inter.mp hy).2⟩⟩
    have h := (card_le_card sub).trans (card_biUnion_le_card_mul _ _ 1 (by
      intro y hy
      rw [card_erase_of_mem ((inStar i y).mpr hy)]
      have := hn y hy
      have := cap y
      omega))
    simp only [card_erase_of_mem (mem_univ i),card_univ,Fintype.card_fin,size,mul_one] at h
    omega
  have partner (i : Fin 8) (z : α) (hz : z ∈ row i) (h3 : (star z).card = 3) :
      ∃ y ∈ row i, (star y).card = 3 ∧ star z ∩ star y = {i} := by
    by_contra! hn
    have sub : univ \ star z ⊆ ((row i).erase z).biUnion (fun y => star y \ star z) := by
      intro j hj
      obtain ⟨y,hy⟩ := meet i j
      have hyj := (inStar j y).mpr (mem_inter.mp hy).2
      have hyz : y ≠ z := fun heq => (mem_sdiff.mp hj).2 (heq ▸ hyj)
      exact mem_biUnion.mpr ⟨y,mem_erase.mpr ⟨hyz,(mem_inter.mp hy).1⟩,mem_sdiff.mpr ⟨hyj,(mem_sdiff.mp hj).2⟩⟩
    have small (y : α) (hy : y ∈ (row i).erase z) : (star y \ star z).card ≤ 1 := by
      have hyi := mem_of_mem_erase hy
      have hi : i ∈ star z ∩ star y := mem_inter.mpr ⟨(inStar i z).mpr hz,(inStar i y).mpr hyi⟩
      have hp := card_pos.mpr ⟨i,hi⟩
      have hc := card_sdiff_add_card_inter (star y) (star z)
      rw [inter_comm] at hc
      by_cases h : (star y).card = 3
      · have hne := hn y hyi h
        have hn1 : (star z ∩ star y).card ≠ 1 := by
          intro heq
          obtain ⟨b,hb⟩ := card_eq_one.mp heq
          have hib : i = b := mem_singleton.mp (hb ▸ hi)
          exact hne (hib ▸ hb)
        omega
      · have := cap y
        omega
    have h := (card_le_card sub).trans (card_biUnion_le_card_mul _ _ 1 small)
    rw [card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin,h3,card_erase_of_mem hz,size] at h
    omega
  let D := (univ.biUnion row).filter fun y => (star y).card = 3
  refine ⟨D.image star,?_,?_,?_⟩
  · intro A hA
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hA
    exact (mem_filter.mp ha).2
  · intro A hA B hB
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hA
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hB
    exact triplesMeet (mem_filter.mp ha).2 (mem_filter.mp hb).2
  · intro i
    obtain ⟨z,hz,h3⟩ := first i
    obtain ⟨y,hy,hy3,hint⟩ := partner i z hz h3
    have incl (a : α) (ha : a ∈ row i) (h : (star a).card = 3) : star a ∈ D.image star :=
      mem_image_of_mem _ (mem_filter.mpr ⟨mem_biUnion.mpr ⟨i,mem_univ _,ha⟩,h⟩)
    exact ⟨star z,incl z hz h3,star y,incl y hy hy3,hint⟩

end EightResidual

namespace Eight

private abbrev Pt := Fin 8
private abbrev Row := Finset Pt
private def left : Row := {0,1,2}
private def right : Row := {0,3,4}
private def candidates (i : Pt) : Finset Row :=
  (univ.powersetCard 3).filter (fun A => i ∈ A ∧ (A ∩ left).Nonempty ∧ (A ∩ right).Nonempty)
private def options (i : Pt) :=
  ((candidates i) ×ˢ (candidates i)).filter (fun p => p.1 ∩ p.2 = {i})
private def compatible (p q : Row × Row) : Prop :=
  (p.1 ∩ q.1).Nonempty ∧ (p.1 ∩ q.2).Nonempty ∧
  (p.2 ∩ q.1).Nonempty ∧ (p.2 ∩ q.2).Nonempty
private instance (p q : Row × Row) : Decidable (compatible p q) := by
  unfold compatible
  infer_instance

private def decode (a : ℕ) : Row := univ.filter (fun x : Pt => a.testBit x.val)
private def asRows (p : ℕ × ℕ) : Row × Row := (decode p.1,decode p.2)
private def orient (xs : List (ℕ × ℕ)) := xs ++ xs.map Prod.swap
private def table5 : List (ℕ × ℕ) :=
  [(35,44),(35,52),(37,42),(37,50),(41,50),(41,52),(42,49),(42,52),(42,97),(42,161),(44,49),(44,50),(44,97),(44,161),(50,97),(50,161),(52,97),(52,161)]
private def table6 : List (ℕ × ℕ) :=
  [(67,76),(67,84),(69,74),(69,82),(73,82),(73,84),(74,81),(74,84),(74,97),(74,193),(76,81),(76,82),(76,97),(76,193),(82,97),(82,193),(84,97),(84,193)]
private def table7 : List (ℕ × ℕ) :=
  [(131,140),(131,148),(133,138),(133,146),(137,146),(137,148),(138,145),(138,148),(138,161),(138,193),(140,145),(140,146),(140,161),(140,193),(146,161),(146,193),(148,161),(148,193)]
private def covers (i : Pt) (xs : List (ℕ × ℕ)) : Prop :=
  options i ⊆ ((orient xs).toFinset.image asRows)
private instance (i : Pt) (xs) : Decidable (covers i xs) := by unfold covers; infer_instance
set_option maxRecDepth 4096 in
private theorem c5 : covers 5 table5 := by decide +kernel
set_option maxRecDepth 4096 in
private theorem c6 : covers 6 table6 := by decide +kernel
set_option maxRecDepth 4096 in
private theorem c7 : covers 7 table7 := by decide +kernel

private def cross (p q : ℕ × ℕ) : Bool :=
  (p.1 &&& q.1 != 0) && (p.1 &&& q.2 != 0) && (p.2 &&& q.1 != 0) && (p.2 &&& q.2 != 0)
private theorem cert :
    (orient table5).all (fun p => (orient table6).all (fun q =>
      !cross p q || (orient table7).all (fun r => !(cross p r && cross q r)))) = true := by
  decide +kernel
private theorem cross_of (p q) (hc : compatible (asRows p) (asRows q)) : cross p q = true := by
  have pos (a b) (h : (decode a ∩ decode b).Nonempty) : (a &&& b != 0) = true := by
    obtain ⟨x,hx⟩ := h
    have ha := (mem_filter.mp (mem_inter.mp hx).1).2
    have hb := (mem_filter.mp (mem_inter.mp hx).2).2
    apply bne_iff_ne.mpr
    intro he
    have hh := congrArg (fun n : ℕ => n.testBit x.val) he
    simp [Nat.testBit_and,ha,hb] at hh
  simp only [cross,Bool.and_eq_true]
  exact ⟨⟨⟨pos _ _ hc.1,pos _ _ hc.2.1⟩,pos _ _ hc.2.2.1⟩,pos _ _ hc.2.2.2⟩
private theorem no_extension (p) (hp : p ∈ options 5) (q) (hq : q ∈ options 6)
    (hpq : compatible p q) (r) (hr : r ∈ options 7) (hc : compatible p r ∧ compatible q r) : False := by
  obtain ⟨a,ha,rfl⟩ := mem_image.mp (c5 hp)
  obtain ⟨b,hb,rfl⟩ := mem_image.mp (c6 hq)
  obtain ⟨d,hd,rfl⟩ := mem_image.mp (c7 hr)
  have h := List.all_eq_true.mp (List.all_eq_true.mp cert a (List.mem_toFinset.mp ha)) b (List.mem_toFinset.mp hb)
  simp only [cross_of _ _ hpq,Bool.not_true,Bool.false_or] at h
  have hh := List.all_eq_true.mp h d (List.mem_toFinset.mp hd)
  simp [cross_of _ _ hc.1,cross_of _ _ hc.2] at hh

private theorem normalized (T : Finset Row) (size : ∀ A ∈ T, A.card = 3)
    (inter : ∀ A ∈ T, ∀ B ∈ T, (A ∩ B).Nonempty)
    (wit : ∀ i : Pt, ∃ A ∈ T, ∃ B ∈ T, A ∩ B = {i})
    (hl : left ∈ T) (hr : right ∈ T) : False := by
  have get (i : Pt) : ∃ p ∈ options i, p.1 ∈ T ∧ p.2 ∈ T := by
    obtain ⟨A,hA,B,hB,hAB⟩ := wit i
    have hi : i ∈ A ∩ B := hAB.symm ▸ mem_singleton_self i
    have inc (D) (hD : D ∈ T) (hiD : i ∈ D) : D ∈ candidates i :=
      mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,size D hD⟩,
        hiD,inter D hD left hl,inter D hD right hr⟩
    exact ⟨(A,B),mem_filter.mpr ⟨mem_product.mpr ⟨inc A hA (mem_inter.mp hi).1,
      inc B hB (mem_inter.mp hi).2⟩,hAB⟩, hA,hB⟩
  have comp (p q : Row × Row) (hp : p.1 ∈ T ∧ p.2 ∈ T)
      (hq : q.1 ∈ T ∧ q.2 ∈ T) : compatible p q :=
    ⟨inter _ hp.1 _ hq.1,inter _ hp.1 _ hq.2,inter _ hp.2 _ hq.1,inter _ hp.2 _ hq.2⟩
  obtain ⟨p,hp,hpt⟩ := get 5
  obtain ⟨q,hq,hqt⟩ := get 6
  obtain ⟨r,hr,hrt⟩ := get 7
  exact no_extension p hp q hq (comp p q hpt hqt) r hr ⟨comp p r hpt hrt,comp q r hqt hrt⟩

private theorem no_eight (T : Finset Row) (size : ∀ A ∈ T, A.card = 3)
    (inter : ∀ A ∈ T, ∀ B ∈ T, (A ∩ B).Nonempty)
    (wit : ∀ i : Pt, ∃ A ∈ T, ∃ B ∈ T, A ∩ B = {i}) : False := by
  classical
  obtain ⟨A,hA,B,hB,hAB⟩ := wit 0
  have h0 : (0 : Pt) ∈ A ∩ B := hAB.symm ▸ mem_singleton_self _
  have ha := (mem_inter.mp h0).1
  have hb := (mem_inter.mp h0).2
  obtain ⟨a,b,_,eA⟩ := card_eq_two.mp (show (A.erase 0).card = 2 by
    rw [card_erase_of_mem ha,size A hA])
  obtain ⟨c,d,_,eB⟩ := card_eq_two.mp (show (B.erase 0).card = 2 by
    rw [card_erase_of_mem hb,size B hB])
  have outside : (univ \ (A ∪ B)).card = 3 := by
    have hs := card_union_add_card_inter A B
    rw [size A hA,size B hB,hAB,card_singleton] at hs
    rw [card_sdiff_of_subset (subset_univ _),card_univ,Fintype.card_fin]
    omega
  obtain ⟨f,g,h,_,_,_,out⟩ := card_eq_three.mp outside
  have aform : A = {0,a,b} := by rw [← eA,insert_erase ha]
  have bform : B = {0,c,d} := by rw [← eB,insert_erase hb]
  let L : Pt → Pt := ![0,a,b,c,d,f,g,h]
  have surj : Function.Surjective L := by
    intro y
    by_cases hya : y ∈ A
    · rw [aform] at hya
      simp only [mem_insert,mem_singleton] at hya
      rcases hya with rfl|rfl|rfl
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩
    by_cases hyb : y ∈ B
    · rw [bform] at hyb
      simp only [mem_insert,mem_singleton] at hyb
      rcases hyb with rfl|rfl|rfl
      · exact ⟨0,rfl⟩
      · exact ⟨3,rfl⟩
      · exact ⟨4,rfl⟩
    have hy : y ∈ univ \ (A ∪ B) := mem_sdiff.mpr ⟨mem_univ _,by simp [hya,hyb]⟩
    rw [out] at hy
    simp only [mem_insert,mem_singleton] at hy
    rcases hy with rfl|rfl|rfl
    · exact ⟨5,rfl⟩
    · exact ⟨6,rfl⟩
    · exact ⟨7,rfl⟩
  let e : Pt ≃ Pt := Equiv.ofBijective L ⟨(Finite.injective_iff_surjective).mpr surj,surj⟩
  let ren (R : Row) := R.map e.symm.toEmbedding
  have ihit (R S : Row) : ren (R ∩ S) = ren R ∩ ren S := map_inter ..
  have lmap : left.map e.toEmbedding = A := by
    rw [aform]
    simp only [left,map_insert,map_singleton]
    rfl
  have rmap : right.map e.toEmbedding = B := by
    rw [bform]
    simp only [right,map_insert,map_singleton]
    rfl
  have back (R : Row) : ren (R.map e.toEmbedding) = R := by simp [ren,map_map]
  apply normalized (T.image ren)
  · intro R hR
    obtain ⟨S,hS,rfl⟩ := mem_image.mp hR
    simpa only [ren,card_map] using size S hS
  · intro R hR S hS
    obtain ⟨A,hA,rfl⟩ := mem_image.mp hR
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hS
    rw [← ihit]
    exact (inter A hA B hB).map
  · intro i
    obtain ⟨R,hR,S,hS,hi⟩ := wit (e i)
    refine ⟨ren R,mem_image_of_mem _ hR,ren S,mem_image_of_mem _ hS,?_⟩
    rw [← ihit,hi]
    simp [ren]
  · exact mem_image.mpr ⟨A,hA,lmap ▸ back left⟩
  · exact mem_image.mpr ⟨B,hB,rmap ▸ back right⟩

end Eight

theorem OMA.orderFiveLowerBound : OMA.R_Erdos21_erdos_21_variants_small_values_R1.H2 := by
  intro F hF
  by_contra! hc
  have h12 : F.card = 12 := by have := OrderFive.twelve_le F hF; omega
  obtain ⟨A,hA,_⟩ := hF.2.2 ∅ (by simp)
  obtain ⟨x,hx⟩ : ∃ x : ℕ, (F.filter (x ∈ ·)).card = 4 := by
    by_contra! hn
    have total := (OrderFive.neighbors hF Subset.rfl hA).trans
      (Finset.sum_le_sum (g := fun _ => 2) (by
        intro x _
        have := OrderFive.degree_limit hF x
        have := hn x
        omega))
    simp [hF.1 A hA,h12] at total
  obtain ⟨T,hsize,hinter,hsingle⟩ := EightResidual.residual h12 hF.1 hF.2.1 hF.2.2 x hx
  exact Eight.no_eight T hsize hinter hsingle

theorem OMA.solution : type_of% @Erdos21.erdos_21.variants.small_values := by
  exact OMA.R_Erdos21_erdos_21_variants_small_values_R1.main OMA.orderFourLowerBound OMA.orderFiveLowerBound
