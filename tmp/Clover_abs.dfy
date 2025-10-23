method Abs(x: int) returns (y: int)
  ensures x < 0 ==> x+y==0
  ensures x>=0 ==> x==y
{
  if x >= 0 {
    y := x;
  } else {
    y:= -x;
  }
}

// SMT Com isolate assertions
// Forma a formula  (x < 0 ==> x+y==0) nega i ver se ela 'e SAT 
// !(x<0 ==> x+y == 0) forma a provar que 'e UNSAT
//  (x<0 && ((x+y) != 0)
  // ele nao encontra contraexamplo 
  // entra no bracjch else
  // (x+y) != 0 && (y==x) 'e unsat next 
  // usou linha y:= -x para esta prova


// Outra assertion
// !(x>=0 ==> x==y) 
// (x>=0 && x!=y)
  // entra no if 
  // y == x && (y!=x) unsat (nao ha forma de nao usar a atribuicao come on!)
  