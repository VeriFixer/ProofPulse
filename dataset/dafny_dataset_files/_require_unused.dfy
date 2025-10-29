// Simple directed graph with vertices of any type T.
class {:autocontracts} Graph<T(==)> {
   var V: set<T>; // vertex-set
   var E: set<(T, T)>; // edge-set

   // Class invariant.
   ghost predicate Valid() {
       // edges must refer to vertices that belong to the vertex-set 
       // and self-loops (edges connecting a vertex to itself) are not allowed 
       forall e :: e in E ==> e.0 in V && e.1 in V && e.0 != e.1
   } 

   // Creates an empty graph.
   constructor ()
     ensures V == {} && E == {}
     {
       V:= {};
       E := {};
     }

   // Adds a new vertex v to this graph.
   method addVertex(v: T)
     requires v !in V //:: UNUSED my proof good Catch  DafnyProjects_tmp_tmp2acw_s4s_Graph.dfy(23,15)-(23,21): requires clause
     ensures E == old(E) && V == old(V) + {v}
     {
        V := V + {v};
     }
}

//:: That require is really not used in proving method correctness. But it is necessary to restrict calling code 
//:: Therefore it should be covered if tested in a good way (one that fails the calling convention!)

method testGraph() {
    var G := new Graph<int>();
    G.addVertex(1); //:: This call should make requires v!in V used (And basically it is really)
    assert G.V == {1};
}


//:: Several erros Appear to be in the report
//:: About requires there are two possibilites: 
//:: - They really are needed to prove something on the method. Like so, in this case they appear directly on the prrof dependencies
method dummy(x:int) returns (y:int)
    requires x == 50
    ensures y == 50
{
    y := x;
}
//:: - They are not needed to prove something on the method. But are needed to restrict calling code (in this case they do not appear covered in their method)
//:: But if other code is calling them they can be covered like. line on
//:: G.addVertex should covere that line as appears on proof dependencies this:  _require_unused.dfy(35,5)-(35,19): requires clause at _require_unused.dfy(23,15)-(23,21) from call
