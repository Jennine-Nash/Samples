(* Name: Jennine Nash
   This was done as a homeowork assignment for my class "Parallel and Sequential Data Structures and Algorithms" in 2013
   The purpose of this program is to, given a graph, return a sequence of all bridges in the graph
    (where a bridge is any edge which is not in a cycle)
 *)

functor MkBridges(structure STSeq : ST_SEQUENCE) : BRIDGES =
struct
  structure Seq = STSeq.Seq
  open STSeq

  type vertex = int
  type edge = vertex * vertex
  type edges = edge Seq.seq

  (* Each element in the sequence is a sequence of the neighbors of the vertex
   * at that index
   *)
  type ugraph = (vertex Seq.seq) Seq.seq

  (* Given a sequence of undirected edges, creates a graph
   * If m is the number of edges, and n is the number of vertices:
   * W(n,m) = O(mlogn)
   * S(n,m) = O(log^2 n)
   *)
  fun makeGraph (E : edge Seq.seq) : ugraph =
    let val opps = Seq.map (fn (u,v) => (v,u)) E
        val es = Seq.append(E, opps)
    in Seq.map (fn (_, s) => s) (Seq.collect Int.compare es)
    end

  (* Given a graph, returns a sequence consisting of all the bridges in the 
   * graph (edges which are not in a cycle)
   * If n is the number of vertices and m is the number of edges:
   * W(n,m) = O(m+n)
   * S(n,m) = O(m+n)
   *)
  fun findBridges (G : ugraph) : edges =
    let val visited = fromSeq(Seq.tabulate (fn i => false) (Seq.length G))
        val tree = fromSeq(Seq.map (fn n => (~1,n)) G)
        val verts = Seq.tabulate (fn i => i) (Seq.length G)

        (* Performs a DFS search on G, renumbering the vertices upon entering,
         * finding cycles upon touching, then using these cycles to find
         * bridges upon exiting
         * p1 p2: both type vertex, 2 previous nodes visited
         * X : bool stseq expressing whether or not each node has been visited
         * T : (vertex seq) stseq which is identical to G except leaves room
         *     for new DFS numberings
         * B : edge list of bridges found
         * i : int, previous DFS vertex number
         * cs : edge list of cycle ranges found (contain no bridges) 
         * v : current vertex
         * Return type: 
         *   bool stseq * (vertex seq) stseq * edge list * int * edge list
         *)
        fun DFS p1 p2 ((X,T,B,i,cs), v) =
          if (nth X v)

               (* Touch: checks if this touch finds a cycle (if v != p1) and
                * either expands the old cycle range to include the new one
                * if they overlap, or adds the new cycle range to cs
                *)
          then let val ((a,b),l) = (hd cs, tl cs) (* Note: cs never empty *)
                   val (c',_) = nth T v
                   val (d',_) = nth T p2
                   val c = Int.min(c',d')
                   val d = Int.max(c',d')
                   val e = if a < c then a else c
                   val f = if b > d then b else d
               in if v = p1 then (X,T,B,i,cs)
                  else if (c > b andalso d > b) orelse (c < a andalso d < a)
                       then (X,T,B,i,(c,d)::cs) 
                       else (X,T,B,i,(e,f)::l)
               end

                  (* Enter: marks v as visited in X, notes v's DFS numbering
                   * in T, and calls DFS on all of v's neighbors
                   *)
          else let val X' = update (v, true) X
                   val (_,n) = nth T v
                   val T' = update (v, (i+1,n)) T
                   val (X'',T'',B',i',cs') = 
                         Seq.iter (DFS p2 v) (X',T',B,i+1,cs) (Seq.nth G v)
                   
                   (* Exit:  Checks if the edge being exited is a bridge
                    * (not in the most recent cycle in cs) and removes the
                    * current cycle from cs if exiting from its lower bound
                    *)
                   val ((c,d),l) = (hd cs', tl cs') (* Note: cs' never empty *)
                   val cs'' = if v = c then l else cs'
               in if ((i+1 >= c andalso i+1 <= d) 
                    andalso (i >= c andalso i <= d)) orelse (p2 = v)
                  then (X'',T'',B',i',cs'')
                  else (X'', T'', (p2,v)::B', i', cs'')
               end

        (* Checks if the current vertex v has already been visited, and if
         * not, r uns the DFS on the connected component containing v to find 
         * its bridges 
         *)
        fun comp ((X,T,B,i,cs), v) =
          if (nth X v) then (X,T,B,i,cs)
          else DFS v v ((X,T,B,~1,[(~1,~1)]), v)

        val (_,_,bridges,_,_) = 
              Seq.iter comp (visited, tree, [], ~1, [(~1,~1)]) verts
    in Seq.fromList(bridges) end

end












