Tests a falhar na avaliacao:
════════════════════════════════════════════════════════════
Task: 82 | File: /home/ricostynha/Desktop/ProofPulse/.eval-tmp/RQ1-GPT4/task_id_82.dfy
────────────────────────────────────────────────────────────
method SphereVolume(radius: real) returns (volume: real)
    requires radius >= 0.0
    ensures volume >= 0.0
{
    volume := (4.0/3.0) * 3.14 * (radius * radius * radius);
}
────────────────────────────────────────────────────────────
Coverage post=strong pre=required inv=none
Oracle   post=weak pre=required inv=-
Overall: coverage=strong oracle=weak FAIL ✗
════════════════════════════════════════════════════════════

Here should have identified invariant as there are code lines not used on this while loop 
════════════════════════════════════════════════════════════
Task: 126 | File: /home/ricostynha/Desktop/ProofPulse/.eval-tmp/RQ1-GPT4/task_id_126.dfy
────────────────────────────────────────────────────────────
method sumOfCommonDivisors(num1: int, num2: int) returns (sum: int)
    requires num1 > 0 && num2 > 0
    ensures sum >= 0
    decreases num1, num2
{
    sum := 0;
    var i: int := 1;
    while i <= num1 && i <= num2
        invariant i >= 0
        decreases num1 - i, num2 - i
    {
        if (num1 % i == 0 && num2 % i == 0) {
            sum := sum + i;
        }
        i := i + 1;
    }
}
────────────────────────────────────────────────────────────
Coverage post=weak pre=optional inv=strong
Oracle   post=weak pre=optional inv=weak
Overall: coverage=weak oracle=weak PASS ✓
════════════════════════════════════════════════════════════

In this as invariants are uncovered this probably should have failed
method IdenticalItemsCount(arr1: array<int>, arr2: array<int>, arr3: array<int>) returns (count: int)
    requires arr1.Length == arr2.Length && arr1.Length == arr3.Length
    ensures 0 <= count && count <= arr1.Length
{
    count := 0;
    var i := 0;
    while i < arr1.Length
    invariant 0 <= i <= arr1.Length
    invariant 0 <= count <= i
    {
        if arr1[i] == arr2[i] && arr2[i] == arr3[i] {
            count := count + 1;
        }
        i := i + 1;
    }
}
────────────────────────────────────────────────────────────
Coverage post=strong pre=required inv=weak
Oracle   post=weak pre=required inv=weak
Overall: coverage=strong oracle=weak FAIL ✗
════════════════════════════════════════════════════════════

There is a linmitation here known in the forall (but need to try to correct it)

════════════════════════════════════════════════════════════
Task: 273 | File: /home/ricostynha/Desktop/ProofPulse/.eval-tmp/RQ1-GPT4/task_id_273.dfy
────────────────────────────────────────────────────────────
method SubtractSeqs(seq1: seq<int>, seq2: seq<int>) returns (res: seq<int>)
  requires |seq1| == |seq2|
  ensures |res| == |seq1|
  ensures forall i :: 0 <= i < |seq1|  ==> res[i] == seq1[i] - seq2[i]
{
  res := [];
  var i := 0;
  while i < |seq1|
    invariant 0 <= i <= |seq1|
    invariant |res| == i
    invariant forall j :: 0 <= j < i ==> res[j] == seq1[j] - seq2[j]
  {
    res := res + [seq1[i] - seq2[i]];
    i := i + 1;
  }
}
────────────────────────────────────────────────────────────
Coverage post=weak pre=required inv=strong
Oracle   post=strong pre=required inv=strong
Overall: coverage=weak oracle=strong FAIL ✗
════════════════════════════════════════════════════════════

Here same problem as with the top and also the new keyword (allocation breaks)

════════════════════════════════════════════════════════════
Task: 282 | File: /home/ricostynha/Desktop/ProofPulse/.eval-tmp/RQ1-GPT4/task_id_282.dfy
────────────────────────────────────────────────────────────
method SubtractArrays(a: array<int>, b: array<int>) returns (c: array<int>)
    requires a.Length == b.Length
    ensures c.Length == a.Length
    ensures forall i :: 0 <= i < c.Length ==> c[i] == a[i] - b[i]
{
    c := new int[a.Length];
    var i: int := 0;
    while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> c[j] == a[j] - b[j]
    {
        c[i] := a[i] - b[i];
        i := i + 1;
    }
}
────────────────────────────────────────────────────────────
Coverage post=weak pre=required inv=strong
Oracle   post=strong pre=required inv=strong
Overall: coverage=weak oracle=strong FAIL ✗
════════════════════════════════════════════════════════════

Atribution (simple assigments coverage bug)
════════════════════════════════════════════════════════════
Task: 309 | File: /home/ricostynha/Desktop/ProofPulse/.eval-tmp/RQ1-GPT4/task_id_309.dfy
────────────────────────────────────────────────────────────
method Max(num1: int, num2: int) returns(max_num: int)
    ensures max_num >= num1 && max_num >= num2 && (max_num == num1 || max_num == num2)
{
     if (num1 > num2) {
        max_num := num1;
    } else {
        max_num := num2;
    }
}
────────────────────────────────────────────────────────────
Coverage post=weak pre=none inv=none
Oracle   post=strong pre=- inv=-
Overall: coverage=weak oracle=strong FAIL ✗
════════════════════════════════════════════════════════════

PRECONDITION PERFECT IDENTIFICATION (Except this)
This is buggy as several are infact not required Xp

method NegativeNumbers(arr: array<int>, negs: array<int>)
    requires arr != null
    requires negs != null
    requires negs.Length == arr.Length
    modifies negs
    ensures forall i :: 0 <= i < arr.Length ==> (arr[i] < 0 ==> negs[i] == arr[i]) && (arr[i] >= 0 ==> negs[i] == 0)
{
    var i := 0;
    while(i < arr.Length)
        invariant 0 <= i <= arr.Length
        invariant forall j :: 0 <= j < i ==> (arr[j] < 0 ==> negs[j] == arr[j]) && (arr[j] >= 0 ==> negs[j] == 0)
    {
        if(arr[i] < 0) {
            negs[i] := arr[i];
        } else {
            negs[i] := 0;
        }
        i := i + 1;
    }
}
────────────────────────────────────────────────────────────
Coverage post=weak pre=required inv=strong
Oracle   post=strong pre=optional inv=strong
Overall: coverage=weak oracle=strong FAIL ✗
════════════════════════════════════════════════════════════




PARA PRE CONDICOES ESTA SIMPLEMENSTE GENIAL OLHA APENAS ESTE\
════════════════════════════════════════════════════════════
Task: 276 | File: /home/ricostynha/Desktop/ProofPulse/.eval-tmp/RQ1-GPT4/task_id_276.dfy
────────────────────────────────────────────────────────────
method CylinderVolume(radius: real, height: real) returns (volume: real)
  requires radius >= 0.0 && height >= 0.0
  ensures volume >= 0.0
{
  volume := 3.141592653589793238 * radius * radius * height;
}
────────────────────────────────────────────────────────────
Coverage post=strong pre=optional inv=none
Oracle   post=strong pre=required inv=-
Overall: coverage=strong oracle=strong PASS ✓
════════════════════════════════════════════════════════════

(diz que nunca usou o radius superior que 0 na prova)
(o que ;e verdade pos radius * rasius é sempre supreior que 0, incrivel)












Melhorias paper FSE

- Fazer dataset com mais de 2 missing asserition e para 

0) Acabar plugin (apenas falta problema de engenharia dos refreshes)

1) Alterar Dataset (especimante de multiplas e +2 assertions e 2):
  -> Focar apenas nas assertions essencias a remover (identifacadas nas assertions helper do grupo 1)
  -> Nao ser exaustivo para o dataset a remover n assertions, Fazer um sampling de varios conjuntos em que se remove n essential assertions do programa.
  O como fazer o sampling pode ser pensado para ter um bom numero de exemplos para todos os diferentes numeros de assertions.

2) Com isto:
  -> Ter uma pre passo onde se preve o numero de assertions a colocar. 
  -> Comparar na prompt colocar sempre 2 (antigo comportamento, o valor real do oraculo, e o valor previsto do melhor metodo de previsao) e ver se performance muda com um numero mais indicado de assertions a colocar. 
  -> Comparar assertions previstas com as selecionadas pelo modelo .
  -> Preparte de prever o numero de assertions pode valorizar bastante. Pois ja nao é preciso fazer hardcoding na prompt de pedir apenas 2 no máximo.

3) Melhorar a prompt com:
  -> indicacoes sobre reveal (by clauses)
  -> Mais exemplos de indexing em assertions
  -> Assinaturas de metodos.lemas.funcoes no ficheiro
  -> Proof idiom simpli:wfication for assertion

4) Experimentar outros modelos, mais o qwen a correr local. Possivelemnte ate fazer fine tuning
