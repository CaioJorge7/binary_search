(*
============================================================

Projeto de Lógica Computacional I
Universidade de Brasília - UnB

Alunos(as): Caio Jorge Soares Viana Jardim/221003921
Eduardo Hermogenes Pinheiro De Moura/221019028
Pablo Rafael Nunes Oliveira/221003986

Tema:
Verificação formal de um algoritmo de inserção ordenada
utilizando o assistente de provas Coq.

Objetivos:

- Implementar um algoritmo de inserção em listas.
- Implementar o algoritmo de Insertion Sort.
- Demonstrar propriedades de corretude utilizando lógica formal.
- Verificar que o algoritmo preserva os elementos da lista
  (Permutation).
- Demonstrar propriedades estruturais do algoritmo.

Observação:

A prova completa da preservação da propriedade Sorted não foi
finalizada devido à quantidade de lemas
auxiliares necessários sobre listas ordenadas.

============================================================
*)

Require Import List.
Require Import Lia.
Require Import Arith.
Require Import PeanoNat.
From Coq Require Import List Permutation.
Require Import Coq.Sorting.Sorted.

Import ListNotations.

Set Implicit Arguments.

(* ------------------------------------------------ *)
(* Busca da posição correta de inserção             *)
(* ------------------------------------------------ *)

(*
A função bsearch percorre uma lista ordenada procurando a
posição onde um novo elemento deve ser inserido.

Nesta implementação ela devolve apenas o índice de inserção.

Exemplo:

Lista: [1;2;4;5]

Inserindo 3

Resultado:

posição = 2
*)

Fixpoint bsearch (x : nat) (l : list nat) : nat :=
  match l with
  | [] => 0
  | h :: t =>
      if x <=? h then
        0
      else
        S (bsearch x t)
  end.

Compute bsearch 3 [1;2;4;5].

(* ------------------------------------------------ *)
(* Inserção em uma posição                          *)
(* ------------------------------------------------ *)

(*
insert_at insere um elemento em uma posição específica da lista.

Exemplo:

insert_at 2 3 [1;2;4;5]

Resultado:

[1;2;3;4;5]
*)

Fixpoint insert_at (i : nat) (x : nat) (l : list nat) :=
  match i, l with
  | 0, _ => x :: l
  | S k, [] => [x]
  | S k, h :: t =>
      h :: insert_at k x t
  end.

Compute insert_at 2 3 [1;2;4;5].

(* ------------------------------------------------ *)
(* Inserção ordenada                                *)
(* ------------------------------------------------ *)

(*
binsert combina duas operações:

1) calcula a posição utilizando bsearch;

2) insere o elemento nessa posição.

Assim obtemos uma inserção em uma lista já ordenada.
*)

Definition binsert (x : nat) (l : list nat) :=
  insert_at (bsearch x l) x l.

Compute binsert 3 [1;2;4;5].

(* ------------------------------------------------ *)
(* Insertion Sort                                   *)
(* ------------------------------------------------ *)

(*
Insertion Sort.

O algoritmo ordena a lista recursivamente.

Primeiro ordena a cauda.

Depois insere o primeiro elemento na posição correta.
*)

Fixpoint binsertion_sort (l : list nat) :=
  match l with
  | [] => []
  | h :: t =>
      binsert h (binsertion_sort t)
  end.

Compute binsertion_sort [5;2;1;4;3].
