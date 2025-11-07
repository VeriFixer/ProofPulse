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
