# Formalization of Polish Mathematical Olympiad Problems

This repository contains unofficial Lean4 formalizations of problems from Polish Mathematical Olympiads, available on [om.sem.edu.pl](om.sem.edu.pl/problems}). Although solutions to the problems are publicly available, the implementations provided here may differ from the model solutions, as some of them represent my individual approaches.

**Disclaimer**: My implementations are surely far from perfect, as I am only learning Lean. It should be also noted that the informal solutions included before each problem may not correspond directly to the formal proof provided alongside.

### Types of Questions

Problems that appear in Polish MO can be briefly categorized into four different groups: geometry, combinatorics, inequalities and number theory. The type of each question is provided in `specs.json`.

### Supplementary lemmas

While the formalizations of all processed questions are available at `PolishMO.problems`, the `PolishMO` folder contains additional files, storing auxiliary statemnts and lemmas that prove useful when attacking the olympiad problems.