

module DATALOG-SYNTAX
	syntax Term ::= String
				|	Id
				|   Int
	
	syntax Terms ::= List{Term,","}
	
	syntax PredicateSymbol ::= Id
	
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
	
  syntax Val ::= String
			 |	 Int
			 
  
  //syntax Maps ::= List{Map,","}
  
    configuration <C>
					<threads>
						<thread multiplicity="*">
							<k> $PGM:Program </k>
							<Datacopy> .Set </Datacopy>
							<Mgu> .Map </Mgu>
																		//if X |-> Y is in the mgu then id2String(X) <String id2String(Y)
																		//if X1 |-> Y1 and X2 |-> Y2 then id2string(X1) =/=String id2String(X2)
							<N> 0 </N>
						</thread>
                    </threads>
                    <Database> .Set </Database>									
					
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

		
	rule [Empty-Literals]:
		<k> .Literals s? => . </k>
		
	rule [Find-Locate-Rule]:
		<k> Find(S:PredicateSymbol ( T:Terms ) ?) ~> X </k>							//fresh variables in T2 and Ls
		<Datacopy>... SetItem(S (T2:Terms) :- Ls:Literals) => . ...</Datacopy>
		<Mgu> M </Mgu>
		<N> N </N>
		(. => <thread>... <k> unifys(T, freshen(N, T2)) ~> freshen(N, Ls) s? ~> X </k> 
						  <Datacopy> .Set </Datacopy>
						  <Mgu> M </Mgu>
						  <N> N +Int 1 </N> ...</thread>) 
		
	
	syntax K ::= freshen(K, K)
	
	rule [Freshen]:
		freshen(A, B) => B [anywhere]
		
	rule [Find-Didnt-Locate-Rule]:
		<k> Find(S1:PredicateSymbol ( T:Terms ) ?) ...</k>							
		<Datacopy>... SetItem(S2:PredicateSymbol (T2:Terms) :- Ls:Literals) => . ...</Datacopy>
		when Id2String(S1) =/=String Id2String(S2)

	rule [Find-Done]:
		<thread>
		<k> Find(S1:PredicateSymbol ( T:Terms ) ?) ...</k>	
		<Datacopy> .Set </Datacopy>
		...</thread> => .
	
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
		
	rule [unify-to-val-new]:
		<k> unify(I:Id, V:Val) => . ...</k>
		<Mgu> M:Map(. => I |-> V) </Mgu>
		when notBool(I in keys(M))
		
	rule [unify-to-val-known]:
		<k> unify(I:Id, V:Val) => . ...</k>
		<Mgu> M:Map(I |-> V) </Mgu>
		
	rule [unify-to-val-continue]:
		<k> unify((I:Id => J), V:Val) ...</k>
		<Mgu> M:Map(I |-> J:Id) </Mgu>
		
	rule [unify-to-val-wrong-order]:
		<k> unify(V:Val, I:Id) => unify(I, V) ...</k>
		
	rule [unify-to-id-wrong-order]:
		<k> unify(I2:Id, I1:Id) => unify(I1, I2) ...</k>
		when Id2String(I1) <String Id2String(I2)
		
	rule [unify-to-id-new]:
		<k> unify(I1:Id, I2:Id) => . ...</k>
		<Mgu> M:Map(. => I1 |-> I2) </Mgu>
		when (Id2String(I1) <String Id2String(I2)) andBool (notBool(I1 in keys(M)))
		
	rule [unify-to-id-known]:
		<k> unify(I1:Id, I2:Id) => unify(I2, V) ...</k>
		<Mgu> M:Map(I1 |-> V:Val) </Mgu>
		when Id2String(I1) <String Id2String(I2)
		
	rule [unify-to-id-known-in-order]:
		<k> unify(I1:Id, I2:Id) => unify(I2, I3) ...</k>
		<Mgu> M:Map(I1 |-> (I3:Id => I2)) </Mgu>
		when (Id2String(I1) <String Id2String(I2)) andBool (Id2String(I2) <String Id2String(I3))
		
	rule [unify-to-id-known-out-of-order]:
		<k> unify(I1:Id, I3:Id) => unify(I2, I3) ...</k>
		<Mgu> M:Map(I1 |-> I2:Id) </Mgu>
		when (Id2String(I1) <String Id2String(I2)) andBool (Id2String(I2) <String Id2String(I3))
		
	
		
	
	

	
	
		


  
endmodule