

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
	
	syntax Queries ::= Literals "s?"
	
	syntax Program ::= Stmt Query
	
endmodule

module DATALOG
  imports DATALOG-SYNTAX
  
  syntax K ::= Sld(Map) | unifys(Terms, Terms) | "does not unify" | "done" |"return" |reverse(Terms) | unify(Term, Term) | Find(Query)
  
  syntax Unification ::= List ":" Term
					 | 	 List ":" "?"
	
  syntax Val ::= String
			 |	 Int
			 
  
  //syntax Maps ::= List{Map,","}
  
    configuration <C>
					<threads>
						<thread multiplicity="*">
							<k> $PGM:Program </k>
							<Datacopy> .Set </Datacopy>
						</thread>
                    </threads>
                    <Database> .Set </Database>
					<Mgu> .Set </Mgu>
					<N> 0 </N>
                </C>
  
  //Cs:Clauses => C, Cs 
	rule [Assertion]:
		<k> ( C:Clause . S:Stmt Q:Query => S Q)</k>
		<Database>... . => SetItem(C) ...</Database>
		
	rule [Assertion-Last-Clause]:
		<k> ( C:Clause . Q:Query => Q ) </k>
		<Database>... . => SetItem(C) ...</Database>
	
	/*
	rule [Query-Locate-Rule]:
		<k> (S:PredicateSymbol ( T:Terms ) ? => unifys(T, T2) ~> Ls s?) ...</k>   //fresh variables in T2 and Ls
		<Database>... SetItem(S (T2:Terms) :- Ls:Literals) ...</Database>								//make a copy of the Database and put into a constructor
	*/																							//iterate through and remove the matches and create new k cells for each
	
	rule [Query-Copy-Data]:
		<k> (S:PredicateSymbol ( T:Terms ) ? => Find(S ( T ) ?)) ...</k>   
		<Database>D:Set</Database>
		<Datacopy> . => D </Datacopy>

	rule [Query-Locate-Rule]:
		<k> Find(S:PredicateSymbol ( T:Terms ) ?) ...</k>							//fresh variables in T2 and Ls
		<Datacopy>... SetItem(S (T2:Terms) :- Ls:Literals) => . ...</Datacopy>
		(. => <thread>... <k> unifys(T, T2) ~> Ls s? </k> <Datacopy> .Set </Datacopy> ...</thread>) //copy the ...
	/*	
	rule [Query-No-Rule]:													//how to write this?
		<k> Find(S:PredicateSymbol ( T:Terms ) ?) => . ...</k>
		<Datacopy>D:Set</Datacopy>
		when SetItem(S (T2:Terms) :- Ls:Literals) inSet D ==Bool false
	*/
	rule [next-rule]:
		<k> L:Literal, Ls:Literals s? => L ? ~> Ls s? ...</k>
		
	rule [Empty-queries]:	
		<k> .Literals => . ...</k>
	
	rule [unify-pair]:
		<k> unifys(T1:Term, T1s:Terms, T2:Term, T2s:Terms) => unify(T1, T2) ~> unifys(T1s, T2s) ...</k> 
		
	rule [unify-empty]:
		<k> unifys(.Terms, .Terms) => . ...</k>
	
	rule [unify-equal]:
		<k> unify(V1:Val, V2:Val) => . ...</k>
		when V1 ==K V2
	
	rule [unify-to-val]:
		<k> unify(I:Id, V:Val) => . ...</k>
		<Mgu>... . => SetItem(ListItem(I) : V) ...</Mgu>
		
	rule [unify-to-val]:
		<k> unify(V:Val, I:Id) => unify(I, V) ...</k>	
	/*	
	rule [unify-to-id]:
		<k> unify(I1:Id, I2:Id) => . ...</k>	
		<Mgu>... SetItem(ListItem(I) : V) ...</Mgu>
	*/
		
	
	
	/*
	
	unify(X,Y)
	
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
		
	
		
	*/

	
	
		


  
endmodule