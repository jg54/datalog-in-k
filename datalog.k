

module DATALOG-SYNTAX
	syntax Term ::= String
				|	Id
				|   Int
	
	syntax Terms ::= List{Term,","}
	
	syntax PredicateSymbol ::= Id
							|  String
	
	syntax Literal ::= PredicateSymbol "(" Terms ")"
					
	syntax Literals ::= List{Literal,","}
					
	syntax Clause ::= Literal ":-" Literals
					
	syntax Clauses ::= List{Clause,","}
					
	syntax Stmt ::= Clause "."
				> 	Clause "." Stmt
	
	syntax Query ::= Literal "?"
	
	syntax Program ::= Stmt Query
	
endmodule

module DATALOG
  imports DATALOG-SYNTAX
  
  syntax K ::= Sld(Map) | unify(Terms, Terms) | "does not unify" | "done" |"return" |reverse(Terms)
  
  syntax Maps ::= List{Map,","}
  
    configuration <C>
                    <k> $PGM:Program </k>
                    <Store> .Set </Store>
					<Mgu> .Map </Mgu>
					<N> 0 </N>
                </C>
  
  //Cs:Clauses => C, Cs 
	rule [Assertion]:
		<k> ( C:Clause . S:Stmt Q:Query => S Q)</k>
		<Store>... . => SetItem(C) ...</Store>
		
	rule [Assertion-Last-Clause]:
		<k> ( C:Clause . Q:Query => Q ) </k>
		<Store>... . => SetItem(C) ...</Store>
	

	rule [Query-Begin]:
		<k> (S:PredicateSymbol ( T:Terms ) ? => S ( T ) ~> Sld(.Map)) ...</k>
	
	rule [Query-Locate-Rule]:
		<k> (S:PredicateSymbol ( T:Terms ) => unify(T, T2) ~> L ~> S ( T )) ~> Sld(_) ...</k>
		<Store>... SetItem(S (T2:Terms) :- L:Literals) ...</Store>
		
	//need to append rules here
	rule [next-rule]:
		<k> (S:PredicateSymbol ( T:Terms ), Ls:Literals => unify(T, T2) ~> L ~> S:PredicateSymbol ( T:Terms ), Ls:Literals) ...</k>
		<Store>... SetItem(S (T2:Terms) :- L:Literals) ...</Store>
		
	rule [Empty-Goal]:
		<k> (.Clauses => done) ...</k>
		
	rule [done-intermediate]:
		<k> (done ~> Sld(_) Ls:Literals => done) ...</k>
		
	rule [done-return]:
		<k> (done ~> Sld(_) L:Literal ~> Sld(.Map) => return ~> L ~> reverse(.Terms)) ...</k>
		
	rule [return-assignvars]:
		<k> (return ~> S:PredicateSymbol ( T:Term, Ts:Terms ) ~> reverse(T1s:Terms) => return ~> S:PredicateSymbol (Ts) ~> reverse(V, T1s)) ...</k>
		<Mgu>M:Map (T |-> V)</Mgu>
		
	rule [return-begin-reverseterms]:
		<k> (return ~> S:PredicateSymbol ( .Terms ) ~> reverse(Ts:Terms) => reverse(Ts:Terms) ~> S (.Terms) ) ...</k>
		
	rule [return-reverseterms]:
		<k> (reverse(T:Term, Ts:Terms) ~> S:PredicateSymbol (T1s:Terms) => reverse(Ts:Terms) ~> S:PredicateSymbol (T, T1s)) ...</k>
		
	rule [return]:
		<k> (reverse(.Terms) ~> S:PredicateSymbol (Ts:Terms) => S (Ts:Terms)) ...</k>
	
	
	//unification
	rule [unify-success]:
		<k> (unify(T:Term, Ts:Terms, T1:Term, T1s:Terms) => unify(Ts, T1s)) ...</k>
		<Mgu>M:Map => M[T / T1]</Mgu>
		when T ==K T1
		
	rule [unify-fail]:
		<k> (unify(T:Term, Ts:Terms, T1:Term, T1s:Terms) => does not unify) ...</k>
		when T =/=K T1
		
	rule [unify-empty]:
		<k> (unify(.Terms, .Terms) ~> Ls:Literals ~> L:Literal => Ls ~> Sld(M) L) ...</k>
		<Mgu>M:Map</Mgu>
		
	rule [unify-empty]:
		<k> (unify(.Terms, .Terms) ~> Ls:Literals ~> L1s:Literals => Ls ~> Sld(M) L1s) ...</k>
		<Mgu>M:Map</Mgu>
	
	rule [doen-not-unify]:
		<k> does not unify ~> _ => false </k>
		
	
		


	
	
		


  
endmodule