# Polynomial-Time Algorithm for 3-SAT: A P = NP Claim

**English** | [Русский](#русский)

## 📌 Abstract & Disclaimer
**Abstract:** This repository presents a proposed polynomial-time algorithm for the **3-SAT** problem, a canonical NP-complete problem. The algorithm is based on propagating **2-CNF constraints** between groups of variables and is claimed to have a time complexity of **O(m⁴)**, where `m` is the number of clauses. If correct, this result implies **P = NP**.

**⚠️ Important Disclaimer:** This is a **pre-print** and a **claim**. It has **not** been peer-reviewed by the scientific community. The purpose of this repository is to facilitate open discussion, verification, and constructive criticism. Serious errors may exist.

## 🚀 Quick Start & Verification
We invite the community to test the algorithm and examine the proof.

1.  **Explore the Proof:** The full theoretical description is provided below in the [**Detailed Description**](#-detailed-description-proof-sketch) section.
2.  **Run the Code:** The implementation of the algorithm can be found in the `/src` directory.
3.  **Test with Examples:** Sample 3-CNF formulas (in DIMACS `.cnf` format) are located in the `/examples` folder.

**How to contribute to the discussion:**
*   To report a bug or potential error in the implementation, open a **GitHub Issue**.
*   To discuss a possible **counterexample** or a flaw in the theoretical proof, open a **GitHub Issue** and provide a detailed explanation or a test case.
*   For general questions, you can use the [GitHub Discussions](https://github.com/gromas/3-SAT-solver-algorithm/discussions) tab.

## 📖 Detailed Description (Proof Sketch)

### 1. Introduction
The **P versus NP** problem is a fundamental open question in computer science. This work claims to resolve it by presenting a polynomial-time algorithm for **3-SAT**, thereby proving **P = NP**. The algorithm employs a novel constraint propagation method that enforces global consistency through local 2-CNF deductions.

### 2. Core Definitions
*   **Formula:** Let `F` be a 3-CNF formula with variables `V` and clauses `C₁, ..., Cₘ`.
*   **Group:** For each clause `C`, define its **group** `G(C)` as the set of its three variables.
*   **Local Assignment:** For a group `G`, `Asgn(G)` is the set of all 8 possible assignments `a: G → {0,1}`.
*   **2-CNF Projection Φ(a):** For an assignment `a ∈ Asgn(G)`, the formula `Φ(a)` is derived by:
    1.  Substituting the values from `a` into `F`.
    2.  Removing satisfied clauses.
    3.  Simplifying the remaining clauses (which now contain at most 2 literals) into a **2-CNF formula** over the variables `V \ G`.
*   **Compatibility:** Two assignments `a ∈ Asgn(G)` and `b ∈ Asgn(H)` are **compatible** iff:
    1.  They agree on all shared variables: `∀x ∈ G ∩ H: a(x) = b(x)`.
    2.  The conjunction of their 2-CNF projections is satisfiable: `Φ(a) ∧ Φ(b)` is satisfiable.

### 3. The Algorithm
The algorithm maintains, for each group `G`, a set of **currently allowed assignments** `A(G) ⊆ Asgn(G)`.

**Step 0: Initialization.**
For each group `G` and each `a ∈ Asgn(G)`, compute `Φ(a)`. If `Φ(a)` is unsatisfiable, discard `a`. Initialize `A(G)` with the remaining assignments. If any `A(G)` becomes empty, halt and return **UNSAT**.

**Step 1: Iterative Constraint Propagation.**
Repeat until no changes occur:
For each group `G`, each `a ∈ A(G)`, and each neighboring group `H` (where `G ∩ H ≠ ∅`):
   1. Find the set `B = { b ∈ A(H) | a and b are compatible }`.
   2. If `B` is empty, remove `a` from `A(G)`.
   3. Otherwise, let `Ψ` be the intersection of all 2-CNF formulas `Φ(b)` for `b ∈ B`. Update `Φ(a) := Φ(a) ∧ Ψ`. If the new `Φ(a)` is unsatisfiable, remove `a` from `A(G)`.
If any `A(G)` becomes empty during this process, halt and return **UNSAT**.

**Step 2: Termination.**
When propagation stabilizes and all `A(G)` are non-empty, return **SAT**. A satisfying assignment can be constructed by consistently combining assignments from the sets `A(G)` (see Lemma 3).

### 4. Proof of Correctness (Sketch)
**Theorem 1 (Soundness):** If the algorithm returns **UNSAT**, the formula `F` is unsatisfiable.
*Proof Sketch:* By induction, any hypothetical satisfying assignment for `F` would induce local assignments that the algorithm could never remove. Contradiction.

**Lemma 2 (Pairwise Compatibility after Propagation):** Upon algorithm termination, for any two groups `G`, `H` and any `a ∈ A(G)`, there exists a compatible `b ∈ A(H)`.
*Proof Sketch:* If `G` and `H` are neighbors, this follows directly from the stopping condition. For non-neighboring groups, compatibility follows by transitivity along a path.

**Lemma 3 (Existence of a Global System):** Upon termination, there exists a system of assignments `{ a_G ∈ A(G) }` that are **pairwise compatible**.
*Proof Sketch (Key Claim):** Constructed by induction on the number of groups. The critical step assumes that for a set of `k` groups, a pairwise compatible system exists. For `k+1` groups, one group `H` is isolated. The induction hypothesis provides a compatible system for the other `k` groups. For each of these `k` groups, by Lemma 2, there is at least one assignment in `A(H)` compatible with it. The central claim is that the **intersection (Ψ)** of the 2-CNF constraints from these compatible assignments in `H` is **satisfiable**, allowing the selection of a consistent `a_H`. **This step requires rigorous justification, as the satisfiability of Ψ does not automatically follow from pairwise compatibility.**

**Theorem 4 (Completeness):** If the algorithm returns **SAT**, the formula `F` is satisfiable.
*Proof Sketch:* By Lemma 3, a pairwise compatible system `{a_G}` exists. A global assignment `τ` is defined by `τ(x) = a_G(x)` for any group `G` containing `x`. Pairwise compatibility ensures `τ` is well-defined. Since each `a_G` does not falsify its original clause, `τ` satisfies all clauses of `F`.

### 5. Complexity Analysis
*   **Initialization (Step 0):** `O(m²)`.
*   **Main Loop (Step 1):** At most `O(m)` iterations. Each iteration processes `O(m)` assignment-group pairs. For each, checking `O(m)` neighbors involves solving a 2-SAT instance (`O(m)`). This leads to **`O(m⁴)`** total worst-case time complexity.

### 6. Open Points & Invitation for Scrutiny
The most critical part of the proof is **Lemma 3**, specifically the claim about the satisfiability of the formula `Ψ`. The community is explicitly invited to:
1.  Analyze the soundness of this inductive construction.
2.  Search for a concrete **counterexample** 3-CNF formula that passes the algorithm's checks but is, in fact, unsatisfiable, or on which the algorithm fails.
3.  Review the complexity analysis for potential oversights.

---

## 🇷🇺 Русский

### 🚀 Краткое описание
В данном репозитории представлен заявленный полиномиальный алгоритм для решения задачи **3-SAT** (NP-полной). Алгоритм основан на распространении **2-CNF ограничений** между группами переменных. Если алгоритм корректен, это доказывает равенство классов сложности **P = NP**.

**⚠️ Важное примечание:** Это **препринт**. Алгоритм и доказательство **не прошли независимую экспертизу** (peer-review). Цель репозитория — открытое обсуждение и проверка сообществом.

### 🔍 Как проверить?
Мы приглашаем всех заинтересованных к проверке.

1.  **Изучите доказательство:** Полное теоретическое описание представлено в разделе [**Detailed Description**](#-detailed-description-proof-sketch) выше.
2.  **Запустите код:** Реализация алгоритма находится в папке `/src`.
3.  **Протестируйте на примерах:** Примеры формул лежат в папке `/examples`.

**Как принять участие в обсуждении:**
*   Чтобы сообщить об ошибке в коде, создайте **Issue** на GitHub.
*   Чтобы обсудить потенциальное **опровержение** или ошибку в доказательстве, создайте **Issue** и приложите подробное описание или тестовый пример.
*   Для общих вопросов используйте вкладку [GitHub Discussions](https://github.com/gromas/3-SAT-solver-algorithm/discussions).

### 📚 Контакт и обсуждение
Основная дискуссия должна вестись публично здесь, на GitHub, через **Issues** и **Discussions**. Это обеспечивает прозрачность и позволяет всем извлечь пользу из замечаний.

---
*This text is provided to facilitate clear scientific discourse. The ultimate validity of the claim depends on rigorous community review.*
