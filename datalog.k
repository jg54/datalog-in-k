

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
  
  syntax K ::= unifys(Terms, Terms) | "does not unify" | unify(Term, Term) | Root(Literal) | print(K) | "active" Literal ":" Literal ":" Literals ":" Literal 	//active" Literal ":" clause":" Normalize(Literals)
			|NormalizeL(Literal)	| Normalize( Int, Map, Terms ) | Sub(Terms, Map) | SubT(Term, Map) | SubLs(Literals, Map) | SubL(Literal, Map)
	
  syntax Val ::= String
			 |	 Int
			 
  
  //syntax Maps ::= List{Map,","}
  
  
	configuration <C>
					<threads>
						<thread multiplicity="*">
							<k> $PGM:Program </k>
							<Used> .Set </Used>
							<Datacopy> .Set </Datacopy>  //remove make database a list copy list into k cell
							<Mgu> .Map </Mgu>
						</thread>
                    </threads>
                    <Database> .Set </Database>	
					<Table> .Set </Table>		
					<printer> .K </printer>
					<originalQuery> .K <originalQuery>
					<globalout stream="stdout"> .List </globalout>
					
                </C>
				
	rule [Assertion]:
		<k> ( C:Clause . S:Stmt Q:Query => S Q)</k>
		<Database>... . => SetItem(C) ...</Database>
		
	rule [Assertion-Last-Clause]:
		<k> ( C:Clause . Q:Query => Q ) </k>
		<Database>... . => SetItem(C) ...</Database>		
	
	rule [Query-Copy-Data]:
		<k> (S:PredicateSymbol ( T:Terms ) ? => Root(S ( Normalize(0, .Map, T) ) )) ...</k>   
		<Datacopy> . => D </Datacopy>
		<Database>D:Set</Database>
		<Table> . => SetItem( S ( Normalize(0, .Map, T) ), . ) </Table>
		
	
	rule [New-Root]:
		<k> Root(S:PredicateSymbol ( T:Terms ) ) </k>
		<Datacopy>... SetItem(S (T2:Terms) :- L:Literal, Ls:Literals) => . ...</Datacopy>   
		(. => <thread>... <k> unifys(T2, T) ~> active S ( T ) : S ( T2 ) : L, Ls : NormalizeL(L) </k> 
						  <Used> .Set </Used>
						  <Datacopy> .Set </Datacopy>
						  <Mgu> .Map </Mgu>
						  ...</thread>) 
						  
	rule [New-Root]:
		<k> Root(S:PredicateSymbol ( Ts:Terms ) ) </k>
		<Datacopy>... SetItem(S (T2s:Terms) :- .Literals) => . ...</Datacopy>
		(. => <thread>... <k> unifys(T2s, Ts) ~> active S ( Ts ) : S ( T2s ) : .Literals : . </k> 
						  <Used> .Set </Used>
						  <Datacopy> .Set </Datacopy>
						  <Mgu> .Map </Mgu>
						  ...</thread>) 
	
	rule [Active-Node-In-Table]:
		<k> active R : H : S:PredicateSymbol ( Ts:Terms ), L, Ls : S1:PredicateSymbol ( T1:Terms ) </k>
		<Used> U:Set => U SetItem(S1 ( T1 ), S2 ( T2 ) )</Used>
		<Table>... SetItem( S1 ( T1 ), S2:PredicateSymbol ( T2:Terms ) ) ...</Table>
		<Mgu> M:Map </Mgu>
		(. => <thread>... <k>unifys(Sub(Ts, M), T2) ~> applySub ~> active R : SubL(H, M): SubLs(L, Ls, M) : NormalizeL(L) </k>  //added applySub
			<Mgu> .Map </Mgu> ...</thread>)
		when notBool (S1 ( T1 ), S2 ( T2 )) in U
		
	rule [Active-Node-In-Table]:
		<k> active R : H : S:PredicateSymbol ( Ts:Terms ), .Literals : S1:PredicateSymbol ( T1:Terms ) </k>
		<Used> U:Set => U SetItem(S1 ( T1 ), S2:PredicateSymbol ( T2:Terms ) )</Used>
		<Table>... SetItem( S1 ( T1 ), S2 ( T2 ) ) ...</Table>
		<Mgu> M:Map </Mgu>
		(. => <thread>... <k>unifys(Sub(Ts, M), T2) ~> active R : SubL(H, M): .Literals : . </k>
			<Mgu> .Map </Mgu> ...</thread>)
		when notBool (S1 ( T1 ), S2 ( T2 )) in U
		
	rule [Active-Node-Not-In-Table]:
		<k> active R : H : L, Ls : S:PredicateSymbol ( Ts:Terms ) </k>
		<Table> T:Set => T SetItem( S ( Ts ), . ) </Table>
		<Database>D:Set</Database>
		(. => <thread>... <k> Root(S ( Ts ))</k>
			<Datacopy> D </Datacopy>
			<Mgu> .Map </Mgu> ...</thread>)
		when notBool (S ( Ts ), .)  in T
		
	rule [Add-Answer-to-Table]:
		<k> active S:PredicateSymbol ( Ts:Terms ) : S1:PredicateSymbol ( T1s:Terms ) : .Literals : . => done</k>
		<Mgu> M:Map </Mgu>
		<Table>... . => SetItem(S ( Normalize(0, .Map, Ts) ), S1 ( Sub(T1s, M) )) ...</Table>
	
	syntax K ::= resolveAmbiguityLiterals(Literals) | resolveAmbiguityTerms(Terms)
	rule resolveAmbiguityLiterals(X) => X [anywhere]
	rule resolveAmbiguityTerms(X) => X [anywhere]
	
	rule [Normalize-Literal]:
		<k> active L1:Literal : L2:Literal : Ls:Literals : (NormalizeL( S:PredicateSymbol ( T:Terms )) => S ( Normalize( 0, .Map, Sub(T, M)) )) </k>
		<Mgu> M:Map </Mgu> 
	
	rule [Sub-Literals]:
		SubLs(L:Literal, Ls:Literals, M:Map) => resolveAmbiguityLiterals(SubL(L, M), SubLs(Ls, M)) [anywhere]
		
	rule [Sub-Literals-Empty]:
		SubLs(.Literals, M:Map) => .Literals [anywhere]
		
	rule [Sub-Literal]:
		SubL(S:PredicateSymbol ( T:Terms ), M:Map) => S ( Sub(T, M) ) [anywhere]
	
	rule [Sub]:
		Sub(T:Term, Ts:Terms, M:Map) => resolveAmbiguityTerms(SubT(T, M), Sub(Ts, M)) [anywhere]
		
	rule [Sub-Empty]:
		Sub(.Terms, M:Map) => .Terms [anywhere]
		
	rule [Sub-Id-In-Map]:
		 SubT(I:Id, M:Map(I |-> X)) => X  [anywhere]

		
	rule [Sub-Id-not-In-Map]:
		SubT(I:Id, M:Map) => I 
		when notBool(I in keys(M)) [anywhere]
		
	rule [Sub-Value]:
		SubT(V:Val, M:Map) => V [anywhere]
		
	rule [Normalize-Terms-Val]:
		Normalize( C:Int, M:Map, V:Val, Ts:Terms) => resolveAmbiguityTerms(V, Normalize(C, M, Ts)) [anywhere]
		
	rule [Normalize-Terms-Id]:
		Normalize(C:Int, M:Map, I:Id, Ts:Terms) => String2Id("X" +String Int2String(C)), Normalize( C +Int 1, M(I |-> String2Id("X" +String Int2String(C))), Ts) 
		when notBool(I in keys(M))[anywhere]
		
	rule [Normalize-Terms-Id]:
		Normalize(C:Int, M:Map(I |-> X:Id), I:Id, Ts:Terms) => X, Normalize( C +Int 1, M, Ts) 

		
	rule [Normalize-Terms-Empty]:
		Normalize(C:Int, M:Map, .Terms) => .Terms [anywhere]
	
	
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
		
	rule [Unify-to-Id]:
		<k> unify(I1:Id, I2:Id) => . ...</k>
		
  
endmodule