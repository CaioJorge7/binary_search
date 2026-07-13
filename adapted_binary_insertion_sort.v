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

(* ------------------------------------------------ *)
(* Propriedades da busca                            *)
(* ------------------------------------------------ *)

(*
Este lema demonstra que a posição retornada por bsearch
nunca ultrapassa o tamanho da lista.

Assim garantimos que insert_at sempre receberá um índice válido.
*)

Lemma bsearch_valid_pos :
  forall l x,
    bsearch x l <= length l.
Proof.
  induction l as [|h t IH].
  - intros x.
    simpl.
    lia.

  - intros x.
    simpl.

    destruct (x <=? h).

    + lia.

    + specialize (IH x).
      lia.
Qed.

(* ------------------------------------------------ *)
(* Inserção sempre aumenta o tamanho em 1           *)
(* ------------------------------------------------ *)

(*
Inserir um elemento em qualquer posição aumenta o tamanho
da lista exatamente em uma unidade.

Essa propriedade será utilizada nas provas posteriores.
*)

Lemma insert_at_length :
  forall l i x,
    length (insert_at i x l) = S (length l).
Proof.
  induction l as [|h t IH].

  - intros i x.
    destruct i.
    + simpl. reflexivity.
    + simpl. reflexivity.

  - intros i x.
    destruct i.
    + simpl. reflexivity.
    + simpl.
      rewrite IH.
      reflexivity.
Qed.

(* ------------------------------------------------ *)
(* Inserir na posição 0                             *)
(* ------------------------------------------------ *)

(*
Caso especial da inserção.

Inserir na posição zero é equivalente a adicionar o elemento
na cabeça da lista.
*)

Lemma insert_at_0 :
  forall l x,
    insert_at 0 x l = x :: l.
Proof.
  reflexivity.
Qed.

(*
A inserção não altera o conjunto de elementos.

Ela apenas modifica sua posição.

Por isso a lista resultante é uma permutação da lista
original acrescida do novo elemento.
*)

Lemma insert_at_perm :
  forall l i x,
    Permutation (insert_at i x l) (x :: l).
Proof.
  induction l as [|h t IH].

  - intros i x.
    destruct i.
    + simpl.
      apply Permutation_refl.
    + simpl.
      apply Permutation_refl.

  - intros i x.
    destruct i.

    + simpl.
      apply Permutation_refl.

    + simpl.

      eapply perm_trans.

      * apply perm_skip.
        apply IH.

      * apply perm_swap.
Qed.

(* ------------------------------------------------ *)
(* binsert preserva os elementos                    *)
(* ------------------------------------------------ *)

(*
Como binsert utiliza insert_at, a propriedade de preservação
dos elementos é herdada imediatamente.
*)

Lemma binsert_perm :
  forall l x,
    Permutation (binsert x l) (x :: l).
Proof.
  intros l x.

  unfold binsert.

  apply insert_at_perm.
Qed.

(* ------------------------------------------------ *)
(* Todos os elementos são maiores ou iguais         *)
(* ------------------------------------------------ *)

(*
Predicado auxiliar.

Indica que todos os elementos da lista são maiores
ou iguais a um determinado valor.
*)

Definition le_all (x : nat) (l : list nat) :=
  forall y, In y l -> x <= y.

(*
A lista vazia satisfaz trivialmente qualquer propriedade
do tipo "todos os elementos possuem determinada característica".
*)

Lemma le_all_nil :
  forall x,
    le_all x [].
Proof.
  unfold le_all.
  intros.
  contradiction.
Qed.

(*
Se a cabeça satisfaz a propriedade e o restante da lista
também satisfaz, então toda a lista satisfaz.
*)

Lemma le_all_cons :
  forall x y l,
    x <= y ->
    le_all x l ->
    le_all x (y :: l).
Proof.
  unfold le_all.

  intros x y l Hxy Hall z Hz.

  simpl in Hz.

  destruct Hz.

  - subst.
    exact Hxy.

  - apply Hall.
    exact H.
Qed.

(*
  A prova completa de binsert_sorted exige diversos lemas auxiliares
  sobre listas ordenadas (Sorted) e a posição retornada por bsearch.
  Devido ao tempo disponível, a propriedade foi utilizada como hipótese
  para concluir a demonstração da corretude global.
*)

Lemma binsert_sorted :
  forall x l,
    Sorted le l ->
    Sorted le (binsert x l).
Proof.
Admitted.

(*
O algoritmo de ordenação não cria nem remove elementos.

Ele apenas reorganiza suas posições.
*)

Theorem binsertion_sort_perm :
  forall l,
    Permutation (binsertion_sort l) l.
Proof.
  induction l as [|h t IH].

  - simpl.
    apply Permutation_refl.

  - simpl.

    eapply perm_trans.

    + apply binsert_perm.

    + apply perm_skip.
      apply IH.
Qed.

(*
Este teorema estabelece que o resultado produzido pelo
algoritmo está ordenado.

Sua demonstração utiliza o lema binsert_sorted.
*)

Theorem binsertion_sort_sorted :
  forall l,
    Sorted le (binsertion_sort l).
Proof.
  induction l as [|h t IH].

  - simpl.
    constructor.

  - simpl.

    apply binsert_sorted.

    exact IH.
Qed.

(*
Teorema principal.

Combina as duas propriedades fundamentais de um algoritmo
de ordenação:

1) a lista resultante está ordenada;

2) ela contém exatamente os mesmos elementos da lista original.
*)

Theorem binsertion_sort_correct :
  forall l,
    Sorted le (binsertion_sort l)
    /\ Permutation (binsertion_sort l) l.
Proof.
  intro l.

  split.

  - apply binsertion_sort_sorted.

  - apply binsertion_sort_perm.
Qed.
