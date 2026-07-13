# Projeto de Lógica Computacional I

## Adaptação da Proposta de Busca Binária: Verificação Formal de Inserção Ordenada em Coq

### Universidade de Brasília (UnB)

**Disciplina:** Lógica Computacional I

**Professor:** Flávio L. C. de Moura

**Integrantes:** Caio Jorge Soares Viana Jardim, Eduardo Hermogenes Pinheiro De Moura, Pablo Rafael Nunes Oliveira

---

# Descrição

Este projeto consiste na implementação e verificação formal de um algoritmo de inserção ordenada utilizando o assistente de provas **Coq**.

O objetivo principal é demonstrar como propriedades matemáticas podem ser utilizadas para garantir a corretude de algoritmos, empregando definições formais, provas interativas e raciocínio lógico.

O algoritmo desenvolvido utiliza uma busca sequencial para determinar a posição de inserção de um elemento em uma lista previamente ordenada. Em seguida, essa operação é utilizada para implementar o algoritmo de ordenação **Insertion Sort**.

---

# Objetivos

* Implementar um algoritmo de busca para determinar a posição de inserção.
* Implementar a inserção de um elemento em qualquer posição da lista.
* Construir o algoritmo de ordenação Insertion Sort.
* Demonstrar propriedades fundamentais utilizando o Coq.
* Formalizar parte da corretude do algoritmo por meio de provas.

---

# Estrutura do Projeto

O desenvolvimento foi organizado em etapas:

## 1. Busca da posição de inserção

Foi implementada a função:

```coq
bsearch
```

Responsável por percorrer uma lista ordenada e retornar a posição onde um novo elemento deve ser inserido.

---

## 2. Inserção em uma posição

Foi implementada a função:

```coq
insert_at
```

Responsável por inserir um elemento em uma posição específica da lista.

---

## 3. Inserção ordenada

Foi implementada a função:

```coq
binsert
```

Esta função combina a busca da posição correta (`bsearch`) com a inserção (`insert_at`).

---

## 4. Algoritmo de ordenação

Foi implementada a função:

```coq
binsertion_sort
```

Responsável por ordenar listas utilizando o algoritmo Insertion Sort.

---

# Testes

Durante o desenvolvimento foram utilizados diversos comandos `Compute` para validar o comportamento das funções.

Exemplos:

```coq
Compute bsearch 3 [1;2;4;5].

Compute insert_at 2 3 [1;2;4;5].

Compute binsert 3 [1;2;4;5].

Compute binsertion_sort [5;2;1;4;3].
```

Os resultados obtidos confirmam o funcionamento esperado das implementações.

---

# Propriedades Formalmente Demonstradas

Foram demonstradas, entre outras, as seguintes propriedades:

## bsearch_valid_pos

Mostra que a posição retornada por `bsearch` nunca ultrapassa o tamanho da lista.

---

## insert_at_length

Demonstra que inserir um elemento aumenta o tamanho da lista em exatamente uma unidade.

---

## insert_at_0

Mostra que inserir na posição zero equivale a adicionar o elemento no início da lista.

---

## insert_at_perm

Demonstra que a inserção apenas reorganiza os elementos da lista, preservando a permutação.

---

## binsert_perm

Mostra que a operação de inserção ordenada também preserva todos os elementos da lista.

---

## le_all_nil

Demonstra que a lista vazia satisfaz trivialmente o predicado auxiliar `le_all`.

---

## le_all_cons

Mostra que, se a cabeça e a cauda satisfazem o predicado `le_all`, então toda a lista também o satisfaz.

---

# Teorema Principal

O projeto possui como objetivo estabelecer a corretude do algoritmo de ordenação através da demonstração simultânea de duas propriedades fundamentais:

* a lista resultante permanece ordenada;
* a lista resultante contém exatamente os mesmos elementos da lista original.

---

# Estado Atual da Formalização

A implementação do algoritmo encontra-se concluída e validada por meio de diversos testes computacionais (`Compute`).

A maior parte das propriedades auxiliares também foi formalmente demonstrada utilizando provas encerradas com `Qed`.

A demonstração completa da preservação da propriedade `Sorted` durante a inserção (`binsert_sorted`) permanece como etapa futura, uma vez que exige lemas adicionais sobre listas ordenadas e sobre a posição calculada pela função `bsearch`.

Mesmo assim, toda a estrutura do algoritmo, suas funções auxiliares e suas principais propriedades encontram-se implementadas e documentadas.

---

# Bibliotecas Utilizadas

* List
* Arith
* Lia
* PeanoNat
* Permutation
* Sorted

---

# Tecnologias

* Coq 8.19.2
* CoqIDE

---

# Considerações Finais

Este projeto permitiu aplicar conceitos de lógica computacional, indução estrutural, listas, relações de ordem e verificação formal utilizando o Coq.

Durante o desenvolvimento foram implementadas funções, construídas provas de propriedades importantes e exploradas técnicas de raciocínio formal sobre algoritmos.

O trabalho também evidenciou como propriedades aparentemente simples, como a preservação da ordenação após uma inserção, podem exigir demonstrações formais bastante elaboradas, reforçando a importância da verificação assistida por computador em sistemas críticos e algoritmos corretos por construção.

